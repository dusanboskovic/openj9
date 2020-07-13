/*******************************************************************************
 * Copyright (c) 1991, 2020 IBM Corp. and others
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at https://www.eclipse.org/legal/epl-2.0/
 * or the Apache License, Version 2.0 which accompanies this distribution and
 * is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following
 * Secondary Licenses when the conditions for such availability set
 * forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
 * General Public License, version 2 with the GNU Classpath
 * Exception [1] and GNU General Public License, version 2 with the
 * OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
 *******************************************************************************/

#include <string.h>

#include "bcvcfr.h"
#include "bcverify.h"
#include "j9bcvnls.h"

#include "cfreader.h"
#include "bcnames.h"
#include "pcstack.h"
#include "j9cp.h"
#include "j9protos.h"
#include "j9consts.h"
#include "omrthread.h"
#include "jvminit.h"
#include "vrfyconvert.h"
#include "bcverify_internal.h"
#include "vrfytbl.h"
#include "vmhook_internal.h"
#include "SCQueryFunctions.h"

#define _UTE_STATIC_
#include "ut_j9bcverify.h"

#include "bcverify.h"

/* Define for debug
#define DEBUG_BCV
*/

#define	BYTECODE_MAP_DEFAULT_SIZE		(2 * 1024)
#define	STACK_MAPS_DEFAULT_SIZE			(2 * 1024)
#define	LIVE_STACK_DEFAULT_SIZE			256
#define	ROOT_QUEUE_DEFAULT_SIZE 		256
#define	CLASSNAMELIST_DEFAULT_SIZE		(128 * sizeof(UDATA *))	/* 128 pointers */
#define	CLASSNAMESEGMENT_DEFAULT_SIZE	1024	/* 1k bytes - minimum of 8 bytes per classNameList entry */

#define BCV_INTERNAL_DEFAULT_SIZE (32*1024)

#define THIS_DLL_NAME J9_VERIFY_DLL_NAME
#define OPT_XVERIFY "-Xverify"
#define OPT_XVERIFY_COLON "-Xverify:"
#define OPT_ALL "all"
#define OPT_OPT "opt"
#define OPT_NO_OPT "noopt"
#define OPT_NO_FALLBACK "nofallback"
#define OPT_IGNORE_STACK_MAPS "ignorestackmaps"
#define OPT_EXCLUDEATTRIBUTE_EQUAL "excludeattribute="
#define OPT_BOOTCLASSPATH_STATIC "bootclasspathstatic"
#define OPT_DO_PROTECTED_ACCESS_CHECK "doProtectedAccessCheck"

static IDATA buildBranchMap (J9BytecodeVerificationData * verifyData);
static IDATA decompressStackMaps (J9BytecodeVerificationData * verifyData, IDATA localsCount, U_8 * stackMapData);
static VMINLINE IDATA parseLocals (J9BytecodeVerificationData * verifyData, U_8** stackMapData, J9BranchTargetStack * liveStack, IDATA localDelta, IDATA localsCount, IDATA maxLocals);
static VMINLINE IDATA parseStack (J9BytecodeVerificationData * verifyData, U_8** stackMapData, J9BranchTargetStack * liveStack, UDATA stackCount, UDATA maxStack);
static UDATA parseElement (J9BytecodeVerificationData * verifyData, U_8 ** stackMapData);
static VMINLINE void copyStack (J9BranchTargetStack *source, J9BranchTargetStack *destination);
static IDATA mergeObjectTypes (J9BytecodeVerificationData *verifyData, UDATA sourceType, UDATA * targetTypePointer);
static IDATA mergeStacks (J9BytecodeVerificationData * verifyData, UDATA target);
static J9UTF8 * mergeClasses(J9BytecodeVerificationData *verifyData, U_8* firstClass, UDATA firstLength, U_8* secondClass, UDATA secondLength, IDATA *reasonCode);
static void bcvHookClassesUnload (J9HookInterface** hook, UDATA eventNum, void* eventData, void* userData);
static void printMethod (J9BytecodeVerificationData * verifyData);
static IDATA simulateStack (J9BytecodeVerificationData * verifyData);

static IDATA parseOptions (J9JavaVM *vm, char *optionValues, char **errorString);
static IDATA setVerifyState ( J9JavaVM *vm, char *option, char **errorString );
static void
printBytes(void * address, IDATA length)
{
	U_8 * tmp = (U_8 *) address;
	IDATA i = 0;
	printf("\n--------------------------------\n");
	printf("Printing from address %p for %d bytes in BIG ENDIAN", address, length);
	for(; i < length; i++) {
		if (0 == (i % (8 * 4))) {
			printf("\n%08X : ", i);
		} else if (0 == i % 4) {
			printf(" ");
		}
		printf("%02X", *(tmp + i));
	}
	printf("\n--------------------------------\n\n");
}

/**
 * Walk the J9-format stack maps and set the uninitialized_this flag appropriately
 * for each map.  It is set to TRUE for the map, if the map's stack contains an
 * uninitialized_this object.
 * NOTE: This is only necessary for <init> methods.
 */
static void 
setInitializedThisStatus(J9BytecodeVerificationData *verifyData)
{
	J9BranchTargetStack * currentStack = NULL;
	IDATA nextMapIndex = 0;

	while (nextMapIndex < verifyData->stackMapsCount) {
		currentStack = BCV_INDEX_STACK (nextMapIndex);
		nextMapIndex++;

		/* Ensure we're not a stack map for dead code */
		if (currentStack->stackBaseIndex != -1) {
			BOOLEAN flag_uninitialized = FALSE;
			IDATA i = 0;
			for (; i < currentStack->stackTopIndex; i++) {
				if ((currentStack->stackElements[i] & BCV_SPECIAL_INIT) == BCV_SPECIAL_INIT) {
					flag_uninitialized = TRUE;
					break;
				}
			}
			currentStack->uninitializedThis = flag_uninitialized;
		}
	}
}



/*
	API
		@verifyData		-	internal data structure
		@firstClass		-	U_8 pointer to class name
		@firstLength	- UDATA length of class name
		@secondClass	-	U_8 pointer to class name
		@secondLength	- UDATA length of class name

	Answer the first common class shared by the two classes.
		If one of the classes is a parent of the other, answer that class.
	Return NULL on error.
		sets reasonCode to BCV_FAIL on verification error
		sets reasonCode to BCV_ERR_INSUFFICIENT_MEMORY on OOM
		sets reasonCode to BCV_ERR_INTERNAL_ERROR otherwise
*/
#define SUPERCLASS(clazz) ((clazz)->superclasses[ J9CLASS_DEPTH(clazz) - 1 ])
static J9UTF8 *
mergeClasses(J9BytecodeVerificationData *verifyData, U_8* firstClass, UDATA firstLength, U_8* secondClass, UDATA secondLength, IDATA *reasonCode)
{
	J9Class *sourceRAM, *targetRAM;
	UDATA sourceDepth, targetDepth;

	/* Go get the ROM class for the source and target.  Check if it returns null immediately to prevent
	 * having to load the second class in an error case */
	sourceRAM = j9rtv_verifierGetRAMClass( verifyData, verifyData->classLoader, firstClass, firstLength, reasonCode);
	if (NULL == sourceRAM) {
		return NULL;
	}

	targetRAM = j9rtv_verifierGetRAMClass( verifyData, verifyData->classLoader, secondClass, secondLength, reasonCode );
	if (NULL == targetRAM) {
		return NULL;
	}
	sourceRAM = J9_CURRENT_CLASS(sourceRAM);
	sourceDepth = J9CLASS_DEPTH(sourceRAM);
	targetDepth = J9CLASS_DEPTH(targetRAM);

	/* walk up the chain until sourceROM == targetROM */
	while( sourceRAM != targetRAM ) {
		if( sourceDepth >= targetDepth ) {
			sourceRAM = SUPERCLASS(sourceRAM);
			if ( sourceRAM ) {
				sourceDepth = J9CLASS_DEPTH(sourceRAM);
			}
		}
		if (sourceRAM == targetRAM )
			break;
		if( sourceDepth <= targetDepth ) {
			targetRAM = SUPERCLASS(targetRAM);
			if ( targetRAM ) {
				targetDepth = J9CLASS_DEPTH(targetRAM);
			}
		}
		if( (sourceRAM == NULL) || (targetRAM == NULL) ) {
			*reasonCode = BCV_FAIL;
			return NULL;
		}
	}

	/* good, both sourceROM and targetROM are the same class -- this is the new target class */
	return( J9ROMCLASS_CLASSNAME( targetRAM->romClass ) );
}
#undef SUPERCLASS


/*
	Determine the number of branch targets in this method.

	Returns
		count of unique branch targets and exception handler starts.
		BCV_ERR_INTERNAL_ERROR for any unexpected error
*/

static IDATA 
buildBranchMap (J9BytecodeVerificationData * verifyData)
{
	J9ROMMethod *romMethod = verifyData->romMethod;
	U_32 *bytecodeMap = verifyData->bytecodeMap;
	U_8 *bcStart;
	U_8 *bcIndex;
	U_8 *bcEnd;
	UDATA npairs, temp;
	IDATA pc, start, high, low, pcs;
	I_16 shortBranch;
	I_32 longBranch;
	UDATA bc, size;
	UDATA count = 0;
	UDATA x = 0;
	
	if (0 == strncmp(J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)), "org/bouncycastle/jce/provider/BouncyCastleProvider", 50) && 0 == strncmp(J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)), "setParameter", 12)) x=1;
	
	bcStart = J9_BYTECODE_START_FROM_ROM_METHOD(romMethod);
	bcIndex = bcStart;
	bcEnd = bcStart + J9_BYTECODE_SIZE_FROM_ROM_METHOD(romMethod);
	
	if(x) {
		printf("b.buildBranchMap - className %.*s methodName %.*s signature : %.*s\n", 
			(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)));
	}
	if(x) printf("b1.verifyData=%p verifyData->bytecodeMap=%p, bcStart=0x%x bcIndex=0x%x bcEnd=0x%x (bcEnd-bcIndex)=%d\n", verifyData, verifyData->bytecodeMap, bcStart, bcIndex, bcEnd, (bcEnd-bcIndex));

	while (bcIndex < bcEnd) {
		bc = *bcIndex;
		size = J9JavaInstructionSizeAndBranchActionTable[bc];
		if(x) printf("b2.\tbcIndex=0x%x bcEnd=0x%x (bcEnd-bcIndex)=%d bc=%x, size=%d\n", bcIndex, bcEnd, (bcEnd-bcIndex), bc, size);
		if (size == 0) {
			verifyData->errorPC = bcIndex - bcStart;
			Trc_BCV_buildBranchMap_UnknownInstruction(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
					bc, verifyData->errorPC, verifyData->errorPC);
			if(x) printf("b3.\tbcIndex=0x%x bcEnd=0x%x (bcEnd-bcIndex)=%d bc=%x, size=%d verifyData->errorPC=%d\n", bcStart, bcIndex, bcEnd, (bcEnd-bcIndex), bc, size, verifyData->errorPC);
			return BCV_ERR_INTERNAL_ERROR;
		}

		switch (size >> 4) {

		case 5: /* switches */
			if (x) printf("b.\tcase 5\n");
			start = bcIndex - bcStart;
			pc = (start + 4) & ~3;
			bcIndex = bcStart + pc;
			longBranch = (I_32) PARAM_32(bcIndex, 0);
			bcIndex += 4;
			if(x) printf("b4.\tstart=%x pc=%x, bcIndex=%x longBranch=%x bytecodeMap[%d]=0x%x\n", start, pc, bcIndex, longBranch, start + longBranch, bytecodeMap[start + longBranch]);
			if (bytecodeMap[start + longBranch] == 0) {
				bytecodeMap[start + longBranch] = BRANCH_TARGET;
				count++;
				if(x) printf("b5.\tFound bytecodeMap[%d] == 0 setting it to %d, count increased to %d\n", start + longBranch, BRANCH_TARGET, count);
			}
			low = (I_32) PARAM_32(bcIndex, 0);
			bcIndex += 4;
			low = (I_32) low;
			if(x) printf("b6.\tlow=%x bcIndex=%x\n", low, bcIndex);
			if (bc == JBtableswitch) {
				high = (I_32) PARAM_32(bcIndex, 0);
				bcIndex += 4;
				high = (I_32) high;
				npairs = (UDATA) (high - low + 1);
				pcs = 0;
				if(x) printf("b7.\tbc(%x) == JBtableswitch (%x) high=%x bcIndex=%x npairs=%x pcs = 0\n", bc, JBtableswitch, high, bcIndex, npairs);
			} else {
				npairs = (UDATA) low;
				pcs = 4;
				if(x) printf("b8.\tbc(%x) != JBtableswitch (%x) npairs=%x pcs = 4\n", bc, JBtableswitch, npairs);
			}

			for (temp = 0; temp < npairs; temp++) {
				bcIndex += pcs;
				longBranch = (I_32) PARAM_32(bcIndex, 0);
				bcIndex += 4;
				if(x) printf("b9.\t\ttemp=%d bcIndex=%x longBranch=%x bytecodeMap[%d]=0x%x\n", temp,bcIndex, longBranch, start + longBranch, bytecodeMap[start + longBranch]);
				if (bytecodeMap[start + longBranch] == 0) {
					bytecodeMap[start + longBranch] = BRANCH_TARGET;
					count++;
					if(x) printf("b10.\t\tbytecodeMap[%d] == 0, set it to %x, count increased to %d\n", start + longBranch, BRANCH_TARGET, count);
				}
			}
			continue;

		case 2: /* gotos */
			if(x) printf("b11.\tcase 2 bc=%x JBgotow=%x\n", bc, JBgotow);
			if (bc == JBgotow) {
				start = bcIndex - bcStart;
				longBranch = (I_32) PARAM_32(bcIndex, 1);
				if(x) printf("b12.\tbc (%x) == JBgotow (%x) start=%x longBranch=%x bytecodeMap[%d]=0x%x\n", bc, JBgotow, start, longBranch, start + longBranch, bytecodeMap[start + longBranch]);
				if (bytecodeMap[start + longBranch] == 0) {
					bytecodeMap[start + longBranch] = BRANCH_TARGET;
					count++;
					if(x) printf("b13.\tbytecodeMap[%d] == 0, set it to %x, count increased to %d\n", start + longBranch, BRANCH_TARGET, count, BRANCH_TARGET);
				}
				break;
			} /* fall through for JBgoto */

		case 1: /* ifs */
			if(x) printf("b14.\tcase 1\n");
			shortBranch = (I_16) PARAM_16(bcIndex, 1);
			start = bcIndex - bcStart;
			if(x) printf("b15.\tshortBranch=%x start=%x bytecodeMap[%d]=0x%x\n", shortBranch, start, start + shortBranch, bytecodeMap[start + shortBranch]);
			if (bytecodeMap[start + shortBranch] == 0) {
				bytecodeMap[start + shortBranch] = BRANCH_TARGET;
				count++;
				if(x) printf("b16.\tbytecodeMap[%d] == 0 set it to %x, count increased to %d\n", start + shortBranch, BRANCH_TARGET, count);
			}
			break;
		}
		bcIndex += size & 7;
		if (x) printf("b.\tincreasing bcIndex to %x size=%d\n", bcIndex, size);
	}

	/* need to walk exceptions as well, since they are branch targets */
	if (romMethod->modifiers & J9AccMethodHasExceptionInfo) {
		J9ExceptionInfo * exceptionData = J9_EXCEPTION_DATA_FROM_ROM_METHOD(romMethod);
		J9ExceptionHandler *handler;
		if(x) printf("b17.\tromMethod->modifiers=%x J9AccMethodHasExceptionInfo=%x exceptionData=%p exceptionData->catchCount=%d\n", romMethod->modifiers, J9AccMethodHasExceptionInfo, exceptionData, exceptionData->catchCount);
		if (exceptionData->catchCount) {
			handler = J9EXCEPTIONINFO_HANDLERS(exceptionData);
			if(x) printf("b18.\texceptionData->catchCount=%d handler=%p\n", exceptionData->catchCount, handler);
			for (temp=0; temp < (U_32) exceptionData->catchCount; temp++) {
				pc = (IDATA) handler->startPC;
				pcs = (IDATA) handler->handlerPC;
				if(x) printf("b19.\t\ttemp=%d pc=%x pcs=%x bytecodeMap[%d]=0x%x\n", temp, pc, pcs, pc, bytecodeMap[pc]);
				/* Avoid re-walking a handler that handles itself */
				if (pc != pcs) {
					bytecodeMap[pc] |= BRANCH_EXCEPTION_START;
					if(x) printf("b20.\t\tpc != pcs, set bytecodeMap[%d] to 0x%x\n", pc, bytecodeMap[pc]);
				}
				if(x) printf("b21.\t\tbytecodeMap[%d]=0x%x\n", pcs, bytecodeMap[pcs]);
				if ((bytecodeMap[pcs] & BRANCH_TARGET) == 0) {
					bytecodeMap[pcs] |= BRANCH_TARGET;
					count++;
					if(x) printf("b22.\t\tBecause (bytecodeMap[pcs] & BRANCH_TARGET) == 0, set bytecodeMap[%d] to 0x%x BRANCH_TARGET=0x%x, count is increased to %d\n", pcs, bytecodeMap[pcs], BRANCH_TARGET, count);
				}
				handler++;
				if(x) printf("b23.\t\thandler is increased to %p\n", handler);
			}
		}
	}
	Trc_BCV_buildBranchMap_branchCount(verifyData->vmStruct,
			(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
			count);
	if(x) printf("b24.\t\treturning count=%d\n", count);
	return count;
}



/*
	Convert the StackMap Attribute maps to internal uncompressed stackmaps.

	Returns
		BCV_SUCCESS on success,
		BCV_FAIL on verification error
*/
static IDATA 
decompressStackMaps (J9BytecodeVerificationData * verifyData, IDATA localsCount, U_8 * stackMapData)
{
	J9ROMMethod *romMethod = verifyData->romMethod;
	UDATA maxStack = J9_MAX_STACK_FROM_ROM_METHOD(romMethod);
	IDATA maxLocals = J9_ARG_COUNT_FROM_ROM_METHOD(romMethod) + J9_TEMP_COUNT_FROM_ROM_METHOD(romMethod);
	UDATA length = (UDATA) J9_BYTECODE_SIZE_FROM_ROM_METHOD(romMethod);
	UDATA i;
	IDATA rc = BCV_SUCCESS;
	J9BranchTargetStack *liveStack = (J9BranchTargetStack *)verifyData->liveStack;
	J9BranchTargetStack *branchTargetStack = BCV_FIRST_STACK();
	U_8 mapType;
	UDATA mapPC = -1;
	UDATA temp;
	UDATA start = 0; /* Used in BUILD_VERIFY_ERROR */
	UDATA mapIndex = 0;
	UDATA errorModule = J9NLS_BCV_ERR_NO_ERROR__MODULE; /* default to BCV NLS catalog */

	Trc_BCV_decompressStackMaps_Entry(verifyData->vmStruct, localsCount);
	/* localsCount records the current locals depth as all stack maps (except full frame) are relative to the previous frame */
	for (i = 0; i < (UDATA) verifyData->stackMapsCount; i++) {
		IDATA localDelta = 0;
		UDATA stackCount = 0;
		
		NEXT_U8(mapType, stackMapData);
		mapPC++;

		if (mapType < CFR_STACKMAP_SAME_LOCALS_1_STACK) {
			/* Same frame 0-63 */
			mapPC += (UDATA) mapType;
			/* done */

		} else if (mapType < CFR_STACKMAP_SAME_LOCALS_1_STACK_END) {
			/* Same with one stack entry frame 64-127 */
			mapPC += (UDATA) ((UDATA) mapType - CFR_STACKMAP_SAME_LOCALS_1_STACK);
			stackCount = 1;

		} else {
			mapPC += NEXT_U16(temp, stackMapData);

			if (mapType == CFR_STACKMAP_SAME_LOCALS_1_STACK_EXTENDED) {
				/* Same with one stack entry extended address frame 247 */
				stackCount = 1;

			} else if (mapType < CFR_STACKMAP_FULL) {
				/* Chop 3-1 locals frame 248-250 */
				/* Same with extended address frame 251 */
				/* Append 1-3 locals frame 252-254 */
				localDelta = ((IDATA) mapType) - CFR_STACKMAP_SAME_EXTENDED;

			} else if (mapType == CFR_STACKMAP_FULL) {
				/* Full frame 255 */
				localDelta = NEXT_U16(temp, stackMapData);
				localsCount = 0;
			}
		}

		localsCount = parseLocals (verifyData, &stackMapData, liveStack, localDelta, localsCount, maxLocals);
		if (localsCount < 0) {
			BUILD_VERIFY_ERROR (errorModule, J9NLS_BCV_ERR_INCONSISTENT_STACK__ID);
			/* Jazz 82615: Set the pc value of the current stackmap frame to show up in the error message frame work */
			liveStack->pc = mapPC;
			verifyData->errorPC = mapPC;

			Trc_BCV_decompressStackMaps_LocalsArrayOverFlowUnderFlow(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
					i, mapPC);
			rc = BCV_FAIL;
			break;
		}

		if (mapType == CFR_STACKMAP_FULL) {
			stackCount = NEXT_U16(temp, stackMapData);
		}

		if (BCV_SUCCESS != parseStack (verifyData, &stackMapData, liveStack, stackCount, maxStack)) {
			BUILD_VERIFY_ERROR (errorModule, J9NLS_BCV_ERR_INCONSISTENT_STACK__ID);
			/* Jazz 82615: Set the pc value of the current stackmap frame to show up in the error message frame work */
			liveStack->pc = mapPC;
			verifyData->errorPC = mapPC;

			Trc_BCV_decompressStackMaps_StackArrayOverFlow(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
					i, mapPC);
			rc = BCV_FAIL;
			break;
		}

		if (mapPC >= length) {
			/* should never get here - caught in staticverify.c checkStackMap */
			BUILD_VERIFY_ERROR (errorModule, J9NLS_BCV_ERR_INCONSISTENT_STACK__ID);
			Trc_BCV_decompressStackMaps_MapOutOfRange(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
					i, mapPC, length);
			rc = BCV_FAIL;
			break;
		}

		(verifyData->bytecodeMap)[mapPC] |= (mapIndex << BRANCH_INDEX_SHIFT) | BRANCH_TARGET;
		mapIndex++;

		copyStack (liveStack, branchTargetStack);
		branchTargetStack->pc = mapPC;
		/* Point to the next stack */
		branchTargetStack = BCV_NEXT_STACK (branchTargetStack);
	}
	
	Trc_BCV_decompressStackMaps_Exit(verifyData->vmStruct, rc);
	return rc;
}



/* Specifically returns BCV_ERR_INTERNAL_ERROR for failure */

static IDATA
parseLocals (J9BytecodeVerificationData * verifyData, U_8** stackMapData, J9BranchTargetStack * liveStack, IDATA localDelta, IDATA localsCount, IDATA maxLocals)
{
	UDATA i;
	UDATA stackEntry;
	UDATA unusedLocals;

	if (localDelta < 0) {
		/* Clear the chopped elements */
		for (;localDelta; localDelta++) {
			localsCount--;
			if (localsCount < 0) {
				goto _underflow;
			}
			liveStack->stackElements[localsCount] = BCV_BASE_TYPE_TOP;

			/* Check long/double type as long as there still remains local variables
			 * in the stackmap frame.
			 */
			if (localsCount > 0) {
				/* Possibly remove a double or long (counts as 1 local, but two slots).
				 * A double or a long is pushed as <top, double|long>
				 */
				stackEntry = liveStack->stackElements[localsCount - 1];
				if ((BCV_BASE_TYPE_DOUBLE == stackEntry) || (BCV_BASE_TYPE_LONG == stackEntry)) {
					localsCount--;
					if (localsCount < 0) {
						goto _underflow;
					}
					liveStack->stackElements[localsCount] = BCV_BASE_TYPE_TOP;
				}
			}
		}

	} else {
		for (;localDelta; localDelta--) {
			stackEntry = parseElement (verifyData, stackMapData);
			if (localsCount >= maxLocals) {
				/* Overflow */
				goto _overflow;
			}
			liveStack->stackElements[localsCount++] = stackEntry;
			if ((BCV_BASE_TYPE_DOUBLE == stackEntry) || (BCV_BASE_TYPE_LONG == stackEntry)) {
				if (localsCount >= maxLocals) {
					/* Overflow */
					goto _overflow;
				}
				liveStack->stackElements[localsCount++] = BCV_BASE_TYPE_TOP;
			}
		}

		/* Clear the remaining locals */
		unusedLocals = liveStack->stackBaseIndex - localsCount;
		for (i = localsCount; i < (unusedLocals + localsCount); i++) {
			liveStack->stackElements[i] = BCV_BASE_TYPE_TOP;
		}
	}

	return localsCount;

_underflow:
	/* Jazz 82615: Set the error code in the case of underflow on 'locals' in the current stackmap frame */
	verifyData->errorDetailCode = BCV_ERR_STACKMAP_FRAME_LOCALS_UNDERFLOW;

	Trc_BCV_parseLocals_LocalsArrayUnderFlow(verifyData->vmStruct,
		(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
		J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
		(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
		J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
		(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
		J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)));
	return BCV_ERR_INTERNAL_ERROR;

_overflow:
	/* Jazz 82615: Set the error code, the location of the last local variable allowed on 'locals'
	 * and the maximum local size in the case of overflow on 'locals' in the currrent stackmap frame.
	 */
	verifyData->errorDetailCode = BCV_ERR_STACKMAP_FRAME_LOCALS_OVERFLOW;
	verifyData->errorCurrentFramePosition = (maxLocals > 0) ? (U_32)(maxLocals - 1) : 0;
	verifyData->errorTempData = (UDATA)maxLocals;

	Trc_BCV_parseLocals_LocalsArrayOverFlow(verifyData->vmStruct,
		(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
		J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
		(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
		J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
		(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
		J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)));
	return BCV_ERR_INTERNAL_ERROR;
}


/*
 * returns BCV_SUCCESS on success
 * returns BCV_ERR_INTERNAL_ERROR on failure
 */

static IDATA
parseStack (J9BytecodeVerificationData * verifyData, U_8** stackMapData, J9BranchTargetStack * liveStack, UDATA stackCount, UDATA maxStack)
{
	UDATA stackEntry;
	UDATA* stackTop = RELOAD_STACKBASE(liveStack); /* Clears the stack */
	UDATA* stackBase = stackTop;

	for (;stackCount; stackCount--) {
		stackEntry = parseElement (verifyData, stackMapData);
		if ((UDATA) (stackTop - stackBase) >= maxStack) {
			/* Jazz 82615: Set the error code and the location of wrong data type on 'stack' (only keep the maximum size for stack) */
			verifyData->errorDetailCode = BCV_ERR_STACKMAP_FRAME_STACK_OVERFLOW;
			verifyData->errorCurrentFramePosition = (U_32)(stackBase - liveStack->stackElements);
			if (maxStack > 0) {
				verifyData->errorCurrentFramePosition += (U_32)(maxStack - 1);
			}
			verifyData->errorTempData = maxStack;
			return BCV_ERR_INTERNAL_ERROR;
		}
		PUSH(stackEntry);
		if ((stackEntry == BCV_BASE_TYPE_DOUBLE) || (stackEntry == BCV_BASE_TYPE_LONG)) {
			if ((UDATA) (stackTop - stackBase) >= maxStack) {
				/* Jazz 82615: Set the error code and the location of wrong data type on 'stack' (only keep the maximum size for stack) */
				verifyData->errorDetailCode = BCV_ERR_STACKMAP_FRAME_STACK_OVERFLOW;
				verifyData->errorCurrentFramePosition = (U_32)(stackBase - liveStack->stackElements);
				if (maxStack > 0) {
					verifyData->errorCurrentFramePosition += (U_32)(maxStack - 1);
				}
				verifyData->errorTempData = maxStack;
				return BCV_ERR_INTERNAL_ERROR;
			}
			PUSH(BCV_BASE_TYPE_TOP);
		}
	}

	SAVE_STACKTOP(liveStack, stackTop);
	return BCV_SUCCESS;
}


/*
 * returns stackEntry
 * No error path in this function
 */

static UDATA
parseElement (J9BytecodeVerificationData * verifyData, U_8** stackMapData)
{
	J9ROMClass * romClass = verifyData->romClass; 
	U_8 entryType;
	U_8 *mapData = *stackMapData;
	U_16 cpIndex;
	UDATA stackEntry;

	NEXT_U8(entryType, mapData);

	if (entryType < CFR_STACKMAP_TYPE_INIT_OBJECT) {
		/* return primitive type */
		stackEntry = verificationTokenDecode[entryType];

	} else if (entryType == CFR_STACKMAP_TYPE_INIT_OBJECT) {
		J9ROMMethod *romMethod = verifyData->romMethod;
		J9UTF8* className = J9ROMCLASS_CLASSNAME(romClass);
		stackEntry = convertClassNameToStackMapType(verifyData, J9UTF8_DATA(className), J9UTF8_LENGTH(className), BCV_SPECIAL_INIT, 0);

	} else if (entryType == CFR_STACKMAP_TYPE_OBJECT) {
		J9UTF8 *utf8string;
		J9ROMConstantPoolItem *constantPool = J9_ROM_CP_FROM_ROM_CLASS(romClass);

		NEXT_U16(cpIndex, mapData);
		utf8string = J9ROMSTRINGREF_UTF8DATA((J9ROMStringRef *) (&constantPool[cpIndex]));
		pushClassType(verifyData, utf8string, &stackEntry);
		
	} else if (entryType == CFR_STACKMAP_TYPE_NEW_OBJECT) {
		NEXT_U16(cpIndex, mapData);
		stackEntry = BCV_SPECIAL_NEW | (((UDATA) cpIndex) << BCV_CLASS_INDEX_SHIFT);

	} else {
		/* Primitive arrays */
		U_16 arity;

		stackEntry = (UDATA) verificationTokenDecode[entryType];
		NEXT_U16(arity, mapData);
		stackEntry |= (((UDATA) arity) << BCV_ARITY_SHIFT);
	}
	
	*stackMapData = mapData;
	return stackEntry;
}
 


static void 
copyStack (J9BranchTargetStack *source, J9BranchTargetStack *destination) 
{
	UDATA pc = destination->pc;

	memcpy((UDATA *) destination, (UDATA *) source, (source->stackTopIndex + BCV_TARGET_STACK_HEADER_UDATA_SIZE) * sizeof(UDATA));

	destination->pc = pc;
}


/* returns
 *  BCV_SUCCESS : no merge necessary
 * 	BCV_FAIL  : cause a rewalk
 * 	BCV_ERR_INSUFFICIENT_MEMORY    : OOM - no rewalk
 */
static IDATA 
mergeObjectTypes (J9BytecodeVerificationData *verifyData, UDATA sourceType, UDATA * targetTypePointer)
{ 
	J9ROMClass * romClass = verifyData->romClass;
	J9ROMMethod *romMethod = verifyData->romMethod;
	UDATA targetType = *targetTypePointer;
	UDATA sourceIndex, targetIndex;  
	J9UTF8 *name;
	UDATA classArity, targetArity, classIndex;
	IDATA rc = BCV_SUCCESS;
	U_8 *sourceName, *targetName;
	UDATA sourceLength, targetLength;
	U_32 *offset;
	IDATA reasonCode = 0;
	UDATA x = 0;
	
	if (0 == strncmp(J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)), "org/bouncycastle/jce/provider/BouncyCastleProvider", 50) && 0 == strncmp(J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)), "setParameter", 12)) x=1;
	if(x) printf("\t\tmot1. verifyData=%p, sourceType=0x%x, targetTypePointer=%p\n", verifyData, sourceType, targetTypePointer);
	
	/* assume that sourceType and targetType are not equal */

	/* if target is more general than source, then its fine */
	rc =  isClassCompatible( verifyData, sourceType, targetType, &reasonCode ) ;

	if (TRUE == rc) {
		if(x) printf("\t\tmot2. TRUE == rc\n");
		return BCV_SUCCESS;	/* no merge required */
	} else { /* FALSE == rc */
		if(x) printf("\t\tmot3. TRUE != rc\n");
		/* VM error, no need to continue, return appropriate rc */
		if (BCV_ERR_INTERNAL_ERROR == reasonCode) {
			*targetTypePointer = (U_32)BCV_JAVA_LANG_OBJECT_INDEX << BCV_CLASS_INDEX_SHIFT;
			Trc_BCV_mergeObjectTypes_UnableToLoadClass(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				sourceType, targetType);
				if(x) printf("\t\tmot4. BCV_ERR_INTERNAL_ERROR(0x%x) == reasonCode(0x%x) sourceType=0x%x, targetType=0x%x\n", BCV_ERR_INTERNAL_ERROR, reasonCode, sourceType, targetType);
			return (IDATA) BCV_FAIL;
		} else if (BCV_ERR_INSUFFICIENT_MEMORY == reasonCode) {
			Trc_BCV_mergeObjectTypes_MergeClasses_OutOfMemoryException(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)));
				if(x) printf("\t\tmot5. BCV_ERR_INSUFFICIENT_MEMORY(0x%x) == reasonCode(0x%x)\n", BCV_ERR_INTERNAL_ERROR, reasonCode);
			return BCV_ERR_INSUFFICIENT_MEMORY;
		}
	}

	/* Types were not compatible, thus target is not equal or more general than source */

	/* NULL always loses to objects */
	if (targetType == BCV_BASE_TYPE_NULL) {
		Trc_BCV_mergeObjectTypes_NullTargetOverwritten(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				sourceType);
		*targetTypePointer = sourceType;
		/* cause a re-walk */
		if(x) printf("\t\tmot6. targetType(0x%x) == BCV_BASE_TYPE_NULL(0x%x) sourceType=0x%x targetTypePointer=%p\n", targetType, BCV_BASE_TYPE_NULL, sourceType, targetTypePointer);
		return (IDATA) BCV_FAIL;
	}

	/* if the source or target are base type arrays, decay them to object arrays of arity n-1 (or just Object) */
	/* Base arrays already have an implicit arity of 1, so just keep the arity for object */
	if (sourceType & BCV_TAG_BASE_ARRAY_OR_NULL) {
		Trc_BCV_mergeObjectTypes_DecaySourceArray(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				sourceType);
		if(x) printf("\t\tmot7. sourceType(0x%x) & BCV_TAG_BASE_ARRAY_OR_NULL(0x%x)\n", sourceType, BCV_TAG_BASE_ARRAY_OR_NULL);
		sourceType = (sourceType & BCV_ARITY_MASK) | ((U_32)BCV_JAVA_LANG_OBJECT_INDEX << BCV_CLASS_INDEX_SHIFT);
		if(x) printf("\t\tmot8. sourceType=0x%x, BCV_ARITY_MASK=0x%x, BCV_JAVA_LANG_OBJECT_INDEX=0x%x, BCV_CLASS_INDEX_SHIFT=0x%x\n", sourceType, BCV_ARITY_MASK, BCV_JAVA_LANG_OBJECT_INDEX, BCV_CLASS_INDEX_SHIFT);
	}

	if (targetType & BCV_TAG_BASE_ARRAY_OR_NULL) {
		Trc_BCV_mergeObjectTypes_DecayTargetArray(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				targetType);
		if(x) printf("\t\tmot9. targetType(0x%x) & BCV_TAG_BASE_ARRAY_OR_NULL(0x%x)\n", targetType, BCV_TAG_BASE_ARRAY_OR_NULL);
		targetType = (targetType & BCV_ARITY_MASK) | ((U_32)BCV_JAVA_LANG_OBJECT_INDEX << BCV_CLASS_INDEX_SHIFT);
		if(x) printf("\t\tmot10. targetType(0x%x) & BCV_ARITY_MASK(0x%x), BCV_JAVA_LANG_OBJECT_INDEX=0x%x, BCV_CLASS_INDEX_SHIFT=0x%x\n", targetType, BCV_ARITY_MASK, BCV_JAVA_LANG_OBJECT_INDEX, BCV_CLASS_INDEX_SHIFT);
	}

	classArity = sourceType & BCV_ARITY_MASK;
	targetArity = targetType & BCV_ARITY_MASK;
	if(x) printf("\t\tmot11. classArity=0x%x, sourceType=0x%x, BCV_ARITY_MASK=0x%x, targetArity=0x%x, targetType=0x%x\n", classArity, sourceType, BCV_ARITY_MASK, targetArity, targetType);

	if (classArity == targetArity) {
		/* Find the common parent class if the same arity */
		if(x) printf("\t\tmot12. classArity(0x%x) == targetArity(0x%x) sourceType=0x%x targetType=0x%x BCV_CLASS_INDEX_MASK=0x%x, BCV_CLASS_INDEX_SHIFT=0x%x\n", classArity, targetArity, sourceType, targetType, BCV_CLASS_INDEX_MASK, BCV_CLASS_INDEX_SHIFT);
		sourceIndex = (sourceType & BCV_CLASS_INDEX_MASK) >> BCV_CLASS_INDEX_SHIFT;
		targetIndex = (targetType & BCV_CLASS_INDEX_MASK) >> BCV_CLASS_INDEX_SHIFT;

		offset = (U_32 *) verifyData->classNameList[sourceIndex];
		sourceLength = (UDATA) J9UTF8_LENGTH(offset + 1);
		if(x) printf("\t\tmot13. sourceIndex=0x%x targetIndex=0x%x offset=%p sourceLength=0x%x\n", sourceIndex, targetIndex, offset, sourceLength);
		if (offset[0] == 0) {
			sourceName = J9UTF8_DATA(offset + 1);
			if(x) printf("\t\tmot14. offset=%p, sourceName=%s\n", offset, sourceName);

		} else {
			sourceName = (U_8 *) ((UDATA) offset[0] + (UDATA) romClass);
			if(x) printf("\t\tmot15. offset=%p, romClass=%p, sourceName=%s\n", offset, romClass, sourceName);
		}
		
		offset = (U_32 *) verifyData->classNameList[targetIndex];
		targetLength = (UDATA) J9UTF8_LENGTH(offset + 1);
		if(x) printf("\t\tmot16. verifyData(%p)->classNameList(%p)[%d] offset=%p targetLength=0x%x\n", verifyData, verifyData->classNameList, verifyData->classNameList[targetIndex], offset, targetLength);
		if (offset[0] == 0) {
			targetName = J9UTF8_DATA(offset + 1);
			if(x) printf("\t\tmot17. 	offset[0] == 0, targetName=%s\n", targetName);
		} else {
			targetName = (U_8 *) ((UDATA) offset[0] + (UDATA) romClass);
			if(x) printf("\t\tmot18. 	offset[0] == 0, romClass=%p, targetName=%s\n", romClass, targetName);
		}

 		name = mergeClasses(verifyData, sourceName, sourceLength, targetName, targetLength, &reasonCode);
		if(x) printf("\t\tmot19. name=%p verifyData, sourceName=%s, sourceLength=0x%x, targetName=%s, targetLength=0x%x, reasonCode=0x%x\n", name, verifyData, sourceName, sourceLength, targetName, targetLength, reasonCode);
 		if (NULL == name) {
 			if(x) printf("\t\tmot20 NULL == name\n");
 			if (BCV_ERR_INSUFFICIENT_MEMORY == reasonCode) {
 				Trc_BCV_mergeObjectTypes_MergeClasses_OutOfMemoryException(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)));
				if(x) printf("\t\tmot21. BCV_ERR_INSUFFICIENT_MEMORY(0x%x) == reasonCode(0x%x)\n", BCV_ERR_INSUFFICIENT_MEMORY, reasonCode);
 				return BCV_ERR_INSUFFICIENT_MEMORY;
 			} else {
 				Trc_BCV_mergeObjectTypes_MergeClassesFail(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
					sourceLength, sourceName, targetLength, targetName);
 				*targetTypePointer = sourceType;
 				/* cause a re-walk */
 				if(x) printf("\t\tmot22. sourceLength=0x%x, sourceName=%s, targetLength=0x%x, targetName=%s sourceType=0x%x targetTypePointer=%p\n", sourceLength, sourceName, targetLength, targetName, sourceType, targetTypePointer);
 				return (IDATA) BCV_FAIL;
 			}
 		}

		classIndex = findClassName( verifyData, J9UTF8_DATA(name), J9UTF8_LENGTH(name) );
		Trc_BCV_mergeObjectTypes_MergeClassesSucceed(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				sourceLength, sourceName, targetLength, targetName, J9UTF8_LENGTH(name), J9UTF8_DATA(name), classIndex);
		if(x) printf("\t\tmot23. sourceLength=0x%x, sourceName=%s, targetLength=0x%x, targetName=%s, J9UTF8_LENGTH(name)=0x%x, J9UTF8_DATA(name)=%s, classIndex=0x%x\n", sourceLength, sourceName, targetLength, targetName, J9UTF8_LENGTH(name), J9UTF8_DATA(name), classIndex);
	} else {

		/* Different arity means common parent class is the minimum arity of class Object */
		classIndex = BCV_JAVA_LANG_OBJECT_INDEX;

		Trc_BCV_mergeObjectTypes_MergeClassesMinimumArity(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				classArity, targetArity);
		/* Find minimum common arity of arrays */ 
		if(x) printf("\t\tmot24. classIndex=0x%x, classArity=0x%x, targetArity=0x%x\n", classIndex, classArity, targetArity);
		if( targetArity < classArity ) {
			if(x) printf("\t\tmot25. targetArity(0x%x) < classArity(0x%x)\n", targetArity, classArity);
			classArity = targetArity;
			if(x) printf("\t\tmot26. classArity(0x%x), targetArity(0x%x)\n", classArity, targetArity);
		}
	}


	/* slam new type into targetTypePointer */
	if(x) printf("\t\tmot27 classArity=0x%x, classIndex=0x%x, BCV_CLASS_INDEX_SHIFT=0x%x\n", classArity, classIndex, BCV_CLASS_INDEX_SHIFT);
	*targetTypePointer = classArity | ( classIndex << BCV_CLASS_INDEX_SHIFT );
	if(x) printf("\t\tmot28. targetTypePointer=%p, *targetTypePointer=0x%x\n", targetTypePointer, *targetTypePointer);
	Trc_BCV_mergeObjectTypes_MergedClass(verifyData->vmStruct,
			(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
			*targetTypePointer);
	/* cause a re-walk */
	if(x) printf("\t\tmot29 return (IDATA) BCV_FAIL;\n");
	return (IDATA) BCV_FAIL;
}

/*
 * returns BCV_SUCCESS on success
 * returns BCV_FAIL on failure
 * returns BCV_ERR_INSUFFICIENT_MEMORY on OOM */
static IDATA 
mergeStacks (J9BytecodeVerificationData * verifyData, UDATA target)
{
	J9ROMClass *romClass = verifyData->romClass;
	J9ROMMethod *romMethod = verifyData->romMethod;
	UDATA maxIndex = J9_ARG_COUNT_FROM_ROM_METHOD(romMethod) + J9_TEMP_COUNT_FROM_ROM_METHOD(romMethod);
	U_32 *bytecodeMap = verifyData->bytecodeMap;
	UDATA i = 0;
	UDATA stackIndex;
	IDATA rewalk = FALSE;
	IDATA rc = BCV_SUCCESS;
	UDATA *targetStackPtr, *targetStackTop, *sourceStackPtr, *sourceStackTop, *sourceStackTemps;
	J9BranchTargetStack *liveStack = (J9BranchTargetStack *) verifyData->liveStack;
	J9BranchTargetStack *targetStack;
	UDATA x = 0;

	if (0 == strncmp(J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)), "org/bouncycastle/jce/provider/BouncyCastleProvider", 50) && 0 == strncmp(J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)), "setParameter", 12)) x=1;

	stackIndex = bytecodeMap[target] >> BRANCH_INDEX_SHIFT;
	targetStack = BCV_INDEX_STACK (stackIndex);
	if(x) {
		printf("m1.\tromClass=%p romMethod=%p maxIndex=0x%x bytecodeMap=%p liveStack=%p J9_ARG_COUNT_FROM_ROM_METHOD(romMethod)=0x%x J9_TEMP_COUNT_FROM_ROM_METHOD(romMethod)=0x%x targetStack->stackBaseIndex=%d\n", 
		              romClass,  romMethod,  maxIndex,     bytecodeMap,   liveStack,    J9_ARG_COUNT_FROM_ROM_METHOD(romMethod),     J9_TEMP_COUNT_FROM_ROM_METHOD(romMethod), targetStack->stackBaseIndex);
	}
	Trc_BCV_mergeStacks_Entry(verifyData->vmStruct,
			(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
			target, target);

	if (targetStack->stackBaseIndex == -1) {

		/* Target location does not have a stack, so give the target our current stack */
		copyStack(liveStack, targetStack);
		verifyData->unwalkedQueue[verifyData->unwalkedQueueTail++] = target;
		verifyData->unwalkedQueueTail %= (verifyData->rootQueueSize / sizeof(UDATA));
		bytecodeMap[target] |= BRANCH_ON_UNWALKED_QUEUE;
		Trc_BCV_mergeStacks_CopyStack(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				stackIndex, target, target);
		if(x) {
			printf("m2.\ttargetStack->stackBaseIndex == -1 verifyData->unwalkedQueue[%d]=0x%x verifyData->unwalkedQueueTail=0x%x bytecodeMap[%d]=0x%x\n",
	                                                       verifyData->unwalkedQueueTail - 1, target, verifyData->unwalkedQueueTail, target, bytecodeMap[target]);
		}
		goto _finished;

	} else {
		UDATA mergePC = (UDATA) -1;
		U_32 resultArrayBase;

		/* Check stack size equality */
		if (targetStack->stackTopIndex != liveStack->stackTopIndex) {
			rc = BCV_FAIL;
			Trc_BCV_mergeStacks_DepthMismatch(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
					stackIndex, target, target,
					liveStack->stackTopIndex, targetStack->stackTopIndex);
			
			printf("About to throw Trc_BCV_mergeStacks_DepthMismatch verifyError\n");
			
			printf("--------- mergeStacks - className %.*s methodName %.*s signature : %.*s, stackIndex=0x%x target=0x%x liveStack->stackTopIndex=0x%x, targetStack->stackTopIndex=0x%x verifyData=%p\n", 
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
				stackIndex, target, liveStack->stackTopIndex, targetStack->stackTopIndex, verifyData);
			printf("------------------------------ Crashing ...................\n");
			*((UDATA *)-1) = 0x321;
			
			goto _finished;
		}

		/* Now we have to merge stacks */
		targetStackPtr = targetStack->stackElements;
		targetStackTop =  RELOAD_STACKTOP(targetStack);
		sourceStackPtr = liveStack->stackElements;
		sourceStackTop = RELOAD_STACKTOP(liveStack);

		/* remember where the temps end */
		sourceStackTemps = RELOAD_STACKBASE(liveStack);
		
		if(x) printf("m3.\ttargetStackPtr=%p targetStackTop=%p sourceStackPtr=%p sourceStackTop=%p sourceStackTemps=%p\n", targetStackPtr, targetStackTop, sourceStackPtr, sourceStackTop, sourceStackTemps);
		Trc_BCV_mergeStacks_MergeStacks(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
				stackIndex, target, target);

		while (sourceStackPtr != sourceStackTop) {
			if(x) printf("m4.\tsourceStackPtr(%p) != sourceStackTop(%p)\n", sourceStackPtr, sourceStackTop);
			/* Merge if the source and target slots are not identical */
			if (*sourceStackPtr != *targetStackPtr) {
				UDATA sourceItem = *sourceStackPtr;
				UDATA targetItem = *targetStackPtr;
				if(x) printf("m5.\tsourceItem=0x%x targetItem=0x%x\n", sourceItem, targetItem);
				/* Merge in the locals */
				if (sourceStackPtr < sourceStackTemps ) {
					if(x) printf("m6.\tsourceStackPtr (%p) < sourceStackTemps (%p)\n", sourceStackPtr, sourceStackTemps);
					/* Merge when either the source or target not an object */
					if ((sourceItem | targetItem) & (BCV_BASE_OR_SPECIAL)) {
						if(x) printf("m7.\t(sourceItem(0x%x) | targetItem(0x%x)) & (BCV_BASE_OR_SPECIAL)(0x%x)\n", sourceItem, targetItem, BCV_BASE_OR_SPECIAL);
						/* Mismatch results in undefined local - rewalk if modified stack
						 * Note: BCV_SPECIAL (specifically BCV_SPECIAL_INIT) must be reserved
						 * to flag the uninitialized_this object existing in the stackmap frame
						 * when invoking setInitializedThisStatus() after the stackmaps is
						 * successfully built.
						 */
						if ((targetItem != (UDATA) (BCV_BASE_TYPE_TOP))
						&& ((targetItem & BCV_SPECIAL) == 0)
						) {
							if(x) printf("m8\t\t(targetItem(0x%x) != (UDATA) (BCV_BASE_TYPE_TOP(0x%x))) && ((targetItem(0x%x) & BCV_SPECIAL(0x%x)) == 0) targetStackPtr=%p *targetStackPtr=0x%x\n", targetItem, (UDATA) (BCV_BASE_TYPE_TOP), targetItem, BCV_SPECIAL, targetStackPtr, *targetStackPtr);
							*targetStackPtr = (UDATA) (BCV_BASE_TYPE_TOP);
							if(x) printf("m8.3\t\ttargetStackPtr=%p *targetStackPtr=0x%x, (UDATA) (BCV_BASE_TYPE_TOP)=0x%x\n", targetStackPtr, *targetStackPtr, (UDATA) (BCV_BASE_TYPE_TOP));
							rewalk = TRUE;
						}

					/* Merge two objects */
					} else {
						if(x) printf("m8.\t}else{\n");
						/* extra checks here to avoid calling local mapper unnecessarily */
						/* Null source or java/lang/Object targets always work trivially */
						if ((*sourceStackPtr != BCV_BASE_TYPE_NULL) && (*targetStackPtr != (BCV_JAVA_LANG_OBJECT_INDEX << BCV_CLASS_INDEX_SHIFT))) {
							if(x) {
								printf("m9.\t(*sourceStackPtr (0x%x) != BCV_BASE_TYPE_NULL(0x%x)) && (*targetStackPtr(0x%x) != (BCV_JAVA_LANG_OBJECT_INDEX (0x%x) << BCV_CLASS_INDEX_SHIFT(0x%x)))\n", 
								              *sourceStackPtr,         BCV_BASE_TYPE_NULL,          *targetStackPtr,          BCV_JAVA_LANG_OBJECT_INDEX,           BCV_CLASS_INDEX_SHIFT);
							}
							/* Null target always causes a re-walk - source is never null here */
							if (*targetStackPtr == BCV_BASE_TYPE_NULL) {
								*targetStackPtr = *sourceStackPtr;
								rewalk = TRUE;
								if(x) printf("m10.\t*targetStackPtr was BCV_BASE_TYPE_NULL, set *targetStackPtr to *sourceStackPtr (0x%x) targetStackPtr=%p sourceStackPtr(%p)\n", *sourceStackPtr, targetStackPtr, sourceStackPtr);
							} else {
								if(x) printf("m11.\t}else{\n");
								/* Use local mapper to check merge necessity in locals */
								if ((verifyData->verificationFlags & J9_VERIFY_OPTIMIZE) && (maxIndex <= 32)) {
									/* Only handle 32 locals or less */
									UDATA index = (UDATA) (sourceStackPtr - liveStack->stackElements);
				if(x) {
					printf("m12.\t(verifyData->verificationFlags(0x%x) & J9_VERIFY_OPTIMIZE(0x%x)) && (maxIndex(%d) <= 32) index(0x%x) = (UDATA) (sourceStackPtr(0x%x) - liveStack->stackElements(0x%x))\n", 
					               verifyData->verificationFlags,       J9_VERIFY_OPTIMIZE,           maxIndex,            index,                 sourceStackPtr, liveStack->stackElements);
				}
									/* Reuse map in this merge if needed for multiple merges at same map */
									if (mergePC == ((UDATA) -1)) {
										mergePC = target;
										if(x) printf("m13.\tmergePC was -1 and then set to target (0x%x)\n", mergePC);
										if (j9localmap_LocalBitsForPC(verifyData->portLib, romClass, romMethod, mergePC, &resultArrayBase, NULL, NULL, NULL) != 0) {
											/* local map error - force a full merge */
											resultArrayBase = (U_32) -1;
											if(x) printf("m14.\tj9localmap_LocalBitsForPC(verifyData->portLib, romClass, romMethod, mergePC, &resultArrayBase, NULL, NULL, NULL) != 0\n");
										} 
									}
									if(x) printf("m15.\t resultArrayBase=0x%x, index=%d\n", resultArrayBase, index);
									if (resultArrayBase & (1 << index)) {
										UDATA origSource = *sourceStackPtr;
										UDATA origTarget = *targetStackPtr;
										IDATA tempRC = mergeObjectTypes(verifyData, *sourceStackPtr, targetStackPtr);
										if(x) printf("m16.\t  origSource=0x%x sourceStackPtr=%p origTarget=0x%x, targetStackPtr=%p tempRC=0x%x\n", origSource, sourceStackPtr, origTarget, targetStackPtr, tempRC);
										/* Merge the objects - the result is live */
										if (BCV_FAIL == tempRC) {
											rewalk = TRUE;
											if(x) printf("m17.\t BCV_FAIL(0x%x) == tempRC(0x%x) rewalk = TRUE\n", BCV_FAIL, tempRC);
										} else if (BCV_ERR_INSUFFICIENT_MEMORY == tempRC) {
											rc = BCV_ERR_INSUFFICIENT_MEMORY; 
											if(x) printf("m18. \t BCV_ERR_INSUFFICIENT_MEMORY == tempRC goto _finished\n");
											goto _finished;
										}

										Trc_BCV_mergeStacks_OptMergeRequired(verifyData->vmStruct,
												(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
												J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
												(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
												J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
												(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
												J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
												origSource, origTarget, *targetStackPtr);
										if(x) printf("m19.\t. origSource=0x%x, origTarget=0x%x, targetStackPtr=%p *targetStackPtr=0x%x\n", origSource, origTarget, targetStackPtr, *targetStackPtr);

									} else {
										Trc_BCV_mergeStacks_OptMergeNotRequired(verifyData->vmStruct,
												(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
												J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
												(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
												J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
												(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
												J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
												*sourceStackPtr, *targetStackPtr);
										/* Tag undefined - local variable is dead */
										*targetStackPtr = (UDATA) (BCV_BASE_TYPE_TOP);
										rewalk = TRUE;
										if(x) printf("m20.\t sourceStackPtr=%p, *sourceStackPtr=0x%x, targetStackPtr=%p, *targetStackPtr=0x%x rewalk = TRUE\n", sourceStackPtr, *sourceStackPtr, targetStackPtr, *targetStackPtr);
									}
								} else {
									if(x) printf("m21.\t verifyData=%p, sourceStackPtr=%p, *sourceStackPtr=0x%x, targetStackPtr=%p\n", verifyData, sourceStackPtr, *sourceStackPtr, targetStackPtr);
									IDATA tempRC =  mergeObjectTypes(verifyData, *sourceStackPtr, targetStackPtr);
									if(x) printf("m22.\t tempRC=0x%x\n", tempRC);
									if (BCV_FAIL == tempRC) {
										rewalk = TRUE;
										if(x) printf("m23.\t BCV_FAIL(0x%x) == tempRC(0x%x)\n", BCV_FAIL, tempRC);
									} else if (BCV_ERR_INSUFFICIENT_MEMORY == tempRC) {
										rc = BCV_ERR_INSUFFICIENT_MEMORY;
										if(x) printf("m24.\t BCV_ERR_INSUFFICIENT_MEMORY(0x%x) == tempRC(0x%x) goto _finished;\n", BCV_ERR_INSUFFICIENT_MEMORY, tempRC);
										goto _finished;
									}
								}
							}
						}
					}

				/* Merge is on the stack */
				} else {
					if(x) printf("m25.\tMerge is on the stack\n");
					if (!((sourceItem | targetItem) & BCV_BASE_OR_SPECIAL)) {
						if(x) printf("m26.\t!((sourceItem(0x%x) | targetItem(0x%x)) & BCV_BASE_OR_SPECIAL(0x%x))\n", sourceItem, targetItem, BCV_BASE_OR_SPECIAL);
						/* Merge two objects */
						IDATA tempRC = mergeObjectTypes(verifyData, *sourceStackPtr, targetStackPtr);
						if(x) printf("m27.\ttempRC=0x%x\n", tempRC);
						if (BCV_FAIL == tempRC) {
							rewalk = TRUE;
							if(x) printf("m28.\tBCV_FAIL(0x%x) == tempRC(0x%x)\n", BCV_FAIL, tempRC);
						} else if (BCV_ERR_INSUFFICIENT_MEMORY == tempRC) {
							rc = BCV_ERR_INSUFFICIENT_MEMORY;
							if(x) printf("m28.\\tBCV_ERR_INSUFFICIENT_MEMORY(0x%x) == tempRC(0x%x) goto _finished;\n", BCV_ERR_INSUFFICIENT_MEMORY, tempRC);
							goto _finished;
						}
					}
				}
			}
			sourceStackPtr++;
			targetStackPtr++;
			if(x) printf("m29.\tsourceStackPtr=%p, targetStackPtr=%p\n", sourceStackPtr, targetStackPtr);
		}
	}

	/* add to the root set if we changed the target stack */
	if (rewalk) {
		if(x) printf("m30.\trewalk=%d\n", rewalk);
		if (!(bytecodeMap[target] & BRANCH_ON_REWALK_QUEUE)) {
			if(x) printf("m31.\t!(bytecodeMap[%d](0x%x) & BRANCH_ON_REWALK_QUEUE(0x%x) verifyData->rewalkQueueTail=%d verifyData->rootQueueSize=%d target=0x%x\n", target, bytecodeMap[target], BRANCH_ON_REWALK_QUEUE, verifyData->rewalkQueueTail, verifyData->rootQueueSize, target);
			Trc_BCV_mergeStacks_QueueForRewalk(verifyData->vmStruct,
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
					target, target);
			verifyData->rewalkQueue[verifyData->rewalkQueueTail++] = target;
			verifyData->rewalkQueueTail %= (verifyData->rootQueueSize / sizeof(UDATA));
			bytecodeMap[target] |= BRANCH_ON_REWALK_QUEUE;
			bytecodeMap[target] &= ~BRANCH_ON_UNWALKED_QUEUE;
			if(x) printf("m31.\tverifyData->rewalkQueue[%d]=0x%x verifyData->rewalkQueueTail=0x%x bytecodeMap[%d]=0x%x\n", verifyData->rewalkQueueTail - 1, verifyData->rewalkQueue[verifyData->rewalkQueueTail - 1], verifyData->rewalkQueueTail, target, bytecodeMap[target]);
		}
	}

_finished:

	Trc_BCV_mergeStacks_Exit(verifyData->vmStruct,
			(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(verifyData->romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_NAME(verifyData->romMethod)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(verifyData->romMethod)),
			rc);
	if(x) printf("m32.\t -------- rc=%d\n", rc);
	return rc;
}





#ifdef DEBUG_BCV
static void 
printMethod (J9BytecodeVerificationData * verifyData)
{
	J9ROMClass *romClass = verifyData->romCLass;
	J9ROMMethod *method = verifyData->romMethod;
	U_8* string;
#if 0
	J9CfrAttributeExceptions* exceptions;
#endif
	IDATA arity, i, j; 
 
	string = J9UTF8_DATA(J9ROMCLASS_CLASSNAME(romClass));
	printf("<");
	for( i=0; i< J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(romClass)); i++ )
	{
		printf( "%c", (string[i] == '/')?'.':string[i]);
	}
	printf(">");

	if( strncmp( string, "java/util/Arrays", i ) == 0 ) {
		printf("stop");
	}
  
	/* Return type. */
	string = J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(method));
	i = 0;
	while(string[i++] != ')');
	arity = 0;
	while(string[i] == '[') arity++, i++;
	switch(string[i])
	{
		case 'B':
			printf( "byte");
			break;

		case 'C':
			printf( "char");
			break;

		case 'D':
			printf( "double");
			break;

		case 'F':
			printf( "float");
			break;

		case 'I':
			printf( "int");
			break;

		case 'J':
			printf( "long");
			break;

		case 'L':
			i++;
			while(string[i] != ';')
			{
				printf( "%c", (string[i] == '/')?'.':string[i]);
				i++;
			}
			break;

		case 'S':
			printf( "short");
			break;

		case 'V':
			printf( "void");
			break;

		case 'Z':
			printf( "boolean");
			break;
	}
	for(i = 0; i < arity; i++)
		printf( "[]");

	printf( " %.*s(", J9UTF8_LENGTH(J9ROMMETHOD_NAME(method)), J9UTF8_DATA(J9ROMMETHOD_NAME(method)));

	for(i = 1; string[i] != ')'; i++)
	{
		arity = 0;
		while(string[i] == '[') arity++, i++;
		switch(string[i])
		{
			case 'B':
				printf( "byte");
				break;

			case 'C':
				printf( "char");
				break;

			case 'D':
				printf( "double");
				break;

			case 'F':
				printf( "float");
				break;

			case 'I':
				printf( "int");
				break;

			case 'J':
				printf( "long");
				break;
		
			case 'L':
				i++;
				while(string[i] != ';')
				{
					printf( "%c", (string[i] == '/')?'.':string[i]);
					i++;
				}
				break;

			case 'S':
				printf( "short");
				break;

			case 'V':
				printf( "void");
				break;

			case 'Z':
				printf( "boolean");
				break;
		}
		for(j = 0; j < arity; j++)
			printf( "[]");

		if(string[i + 1] != ')')
			printf( ", ");
	}

	printf( ")");
#if 0	/* need to fix this code to work with J9ROMMethods.. */
	for(i = 0; i < method->attributesCount; i++)
	{
		if(method->attributes[i]->tag == CFR_ATTRIBUTE_Exceptions)
		{
			exceptions = (J9CfrAttributeExceptions*)method->attributes[i];

			printf( " throws ");
			for(j = 0; j < exceptions->numberOfExceptions - 1; j++)
			{
				if(exceptions->exceptionIndexTable[j] != 0)
				{
					index = classfile->constantPool[exceptions->exceptionIndexTable[j]].slot1;
					string = classfile->constantPool[index].bytes;
					while(*string)
					{
						printf( "%c", (*string == '/')?'.':*string);
						string++;
					}
					printf( ", ");
				}
			}
			index = classfile->constantPool[exceptions->exceptionIndexTable[j]].slot1;
			string = classfile->constantPool[index].bytes;
			while(*string)
			{
				printf( "%c", (*string == '/')?'.':*string);
				string++;
			}

			i = method->attributesCount;
		}
	}	
#endif
	printf( ";\n");
	return;
}


#endif

/*
 * return BCV_SUCCESS on success
 * returns BCV_ERR_INTERNAL_ERROR on any errors
 * returns BCV_ERR_INSUFFICIENT_MEMORY on OOM

*/

static IDATA 
simulateStack (J9BytecodeVerificationData * verifyData)
{

#define CHECK_END \
	if(pc > length) { \
		errorType = J9NLS_BCV_ERR_UNEXPECTED_EOF__ID;	\
		verboseErrorCode = BCV_ERR_UNEXPECTED_EOF;	\
		goto _verifyError; \
	}

	J9ROMClass * romClass = verifyData->romClass;
	J9ROMMethod * romMethod = verifyData->romMethod;
	J9BranchTargetStack * liveStack = (J9BranchTargetStack *) verifyData->liveStack;
	U_32 * bytecodeMap = verifyData->bytecodeMap;
	IDATA start = 0;
	UDATA pc = 0;
	UDATA length, index, target;
	J9ROMConstantPoolItem *constantPool;
	J9ROMConstantPoolItem *info;
	J9UTF8 *utf8string;
	U_8 *code;
	U_8 *bcIndex;
	UDATA bc = 0;
	UDATA popCount, type1, type2, action;
	UDATA type, temp1, temp2, temp3, maxStack;
	UDATA justLoadedStack = FALSE;
	UDATA *stackBase;
	UDATA *stackTop;
	UDATA *temps;
	UDATA stackIndex;
	UDATA wideIndex = FALSE;
	UDATA *ptr;
	IDATA i1, i2;
	UDATA classIndex;
	UDATA errorModule = J9NLS_BCV_ERR_NO_ERROR__MODULE; /* default to BCV NLS catalog */
	U_16 errorType;
	I_16 offset16;
	I_32 offset32;
	J9BranchTargetStack * branch;
	UDATA checkIfInsideException = romMethod->modifiers & J9AccMethodHasExceptionInfo;
	UDATA tempStoreChange;
	J9ExceptionInfo *exceptionData = J9_EXCEPTION_DATA_FROM_ROM_METHOD(romMethod);
	J9ExceptionHandler *handler;
	UDATA exception;
	J9SRP *callSiteData = (J9SRP *) J9ROMCLASS_CALLSITEDATA(romClass);
	UDATA* originalStackTop;
	UDATA originalStackZeroEntry;
	/* Jazz 104084: Initialize verification error codes by default */
	IDATA verboseErrorCode = 0;
	UDATA errorTargetType = (UDATA)-1;
	UDATA errorStackIndex = (UDATA)-1;
	UDATA errorTempData = (UDATA)-1;
	UDATA x = 0;	

	Trc_BCV_simulateStack_Entry(verifyData->vmStruct);

	if (0 == strncmp(J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)), "org/bouncycastle/jce/provider/BouncyCastleProvider", 50) && 0 == strncmp(J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)), "setParameter", 12)) x=1;
	if(x) {
		printf("\ts0. verifyData=%p romClass=%p romMethod=%p liveStack=%p, bytecodeMap=%p checkIfInsideException=0x%x exceptionData=0x%x callSiteData=%p\n", 
		             verifyData, romClass, romMethod,       liveStack,   bytecodeMap,    checkIfInsideException,    exceptionData,      callSiteData);
	}
#ifdef DEBUG_BCV
	printMethod(verifyData);
#endif

	verifyData->unwalkedQueueHead = 0;
	verifyData->unwalkedQueueTail = 0;
	verifyData->rewalkQueueHead = 0;
	verifyData->rewalkQueueTail = 0;

	code = J9_BYTECODE_START_FROM_ROM_METHOD(romMethod);
	length = (UDATA) J9_BYTECODE_SIZE_FROM_ROM_METHOD(romMethod);
	maxStack = J9_MAX_STACK_FROM_ROM_METHOD(romMethod);
	if(x) printf("s1. code=%p, length=%d, maxStack=0x%x\n", code, length, maxStack);
	/* Jazz 105041: Initialize the 1st data slot on 'stack' with 'top' (placeholdler)
	 * to avoid storing garbage data type in the error message buffer
	 * when stack underflow occurs.
	 */
	liveStack->stackElements[liveStack->stackBaseIndex] = BCV_BASE_TYPE_TOP;

	RELOAD_LIVESTACK;

	bcIndex = code;

	constantPool = J9_ROM_CP_FROM_ROM_CLASS(romClass);
	if(x) printf("\ts1. bcIndex = code=%p, constantPool=%p\n", bcIndex, constantPool);
	while (pc < length) {
		if(x) printf("\ts2.pc(0x%x) < length(0x%x)\n", pc, length);	
		if ((UDATA) (stackTop - stackBase) > maxStack) {
			if(x) printf("\ts3.(stackTop(%p) - stackBase(%p)) > maxStack(0x%x)\n", stackTop, stackBase, maxStack);	
			errorType = J9NLS_BCV_ERR_STACK_OVERFLOW__ID;
			verboseErrorCode = BCV_ERR_STACK_OVERFLOW;
			SAVE_STACKTOP(liveStack, stackTop);
			if(x) printf("\ts4.\n");	
			goto _verifyError;
		}

		/* If exception start PC, or possible branch to inside an exception range, */
		/*  copy the existing stack shape into the exception stack */
		if ((bytecodeMap[pc] & BRANCH_EXCEPTION_START) || (justLoadedStack && checkIfInsideException)) {
			if(x) printf("\ts5.(bytecodeMap[%d](0x%x) & BRANCH_EXCEPTION_START(0x%x)) || (justLoadedStack(%d) && checkIfInsideException(%d))\n", pc, bytecodeMap[pc], BRANCH_EXCEPTION_START, justLoadedStack, checkIfInsideException);
			handler = J9EXCEPTIONINFO_HANDLERS(exceptionData);
			SAVE_STACKTOP(liveStack, stackTop);

			/* Save the current liveStack element zero */
			/* Reset the stack pointer to push the exception on the empty stack */
			originalStackTop = stackTop;
			originalStackZeroEntry = liveStack->stackElements[liveStack->stackBaseIndex];
			if(x) printf("\ts6.originalStackTop = stackTop=%p originalStackZeroEntry=0x%x liveStack->stackElements[%d]=0x%x\n", originalStackTop, originalStackZeroEntry, liveStack->stackBaseIndex, liveStack->stackElements[liveStack->stackBaseIndex]);
			for (exception = 0; exception < (UDATA) exceptionData->catchCount; exception++) {
				if(x) printf("\ts7.exception=%d exceptionData->catchCount=%d\n", exception, exceptionData->catchCount);
			
				/* find the matching branch target, and copy/merge the stack with the exception object */
				if ((pc >= handler->startPC) && (pc < handler->endPC)) {
#ifdef DEBUG_BCV
					printf("exception startPC: %d\n", handler->startPC);
#endif
					if(x) printf("\ts8.(pc(0x%x) >= handler->startPC(0x%x)) && (pc(0x%x) < handler->endPC(0x%x))\n", pc, handler->startPC, pc < handler->endPC);
					stackIndex = bytecodeMap[handler->handlerPC] >> BRANCH_INDEX_SHIFT;
					branch = BCV_INDEX_STACK (stackIndex);
					if(x) printf("\ts9. stackIndex(0x%x) = bytecodeMap[%d](0x%x) >> BRANCH_INDEX_SHIFT(0x%x)\n", stackIndex, handler->handlerPC, bytecodeMap[handler->handlerPC], BRANCH_INDEX_SHIFT);
					/* "push" the exception object */
					classIndex = BCV_JAVA_LANG_THROWABLE_INDEX;
					if(x) printf("\ts10. classIndex=BCV_JAVA_LANG_THROWABLE_INDEX=0x%x\n", classIndex);
					if (handler->exceptionClassIndex) {
						/* look up the class in the constant pool */
						utf8string = J9ROMSTRINGREF_UTF8DATA((J9ROMStringRef *)(&constantPool [handler->exceptionClassIndex]));
						if(x) printf("\ts11. utf8string=%p constantPool=%p, handler->exceptionClassIndex=%d\n", utf8string, constantPool, handler->exceptionClassIndex);
						classIndex = findClassName(verifyData, J9UTF8_DATA(utf8string), J9UTF8_LENGTH(utf8string));
						if(x) printf("\ts12. handler->exceptionClassIndex=%d utf8string=%p classIndex=0x%x\n", handler->exceptionClassIndex, utf8string, classIndex);
					}

					/* Empty the stack */
					stackTop = &(liveStack->stackElements[liveStack->stackBaseIndex]);
					if(x) printf("\ts13. stackTop=%p liveStack=%p classIndex=0x%x BCV_CLASS_INDEX_SHIFT=%d\n", stackTop, liveStack, classIndex, BCV_CLASS_INDEX_SHIFT);
					PUSH(classIndex << BCV_CLASS_INDEX_SHIFT);
					SAVE_STACKTOP(liveStack, stackTop);
					
					if(x) printf("\ts14. before calling mergeStacks (verifyData(%p), handler->handlerPC(0x%x)), handle=%p\n", verifyData, handler->handlerPC, handler);
					if (BCV_ERR_INSUFFICIENT_MEMORY == mergeStacks (verifyData, handler->handlerPC)) {
						errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID;
						if(x) printf("\ts15. BCV_ERR_INSUFFICIENT_MEMORY(%d)\n", BCV_ERR_INSUFFICIENT_MEMORY);
						goto _outOfMemoryError;
					}
					if(x) printf("\ts16.\n");
				}
				handler++;
				if(x) printf("\ts17. handler=%p\n", handler);
			}

			if(x) printf("\ts18. liveStack(%p)->stackElements[%d]=0x%x, originalStackZeroEntry\n", liveStack, liveStack->stackBaseIndex, liveStack->stackElements[liveStack->stackBaseIndex], originalStackZeroEntry);
			/* Restore liveStack */
			liveStack->stackElements[liveStack->stackBaseIndex] = originalStackZeroEntry;
			if(x) printf("\ts19. liveStack(%p)->stackElements[%d]= 0x%x = originalStackZeroEntry, stackTop=%p, originalStackTop=%p\n", liveStack, liveStack->stackBaseIndex, liveStack->stackElements[liveStack->stackBaseIndex], originalStackZeroEntry, stackTop, originalStackTop);
			stackTop = originalStackTop;
			if(x) printf("\ts20. stackTop = originalStackTop=%p\n", stackTop);
		}
		if(x) printf("\ts21. start=0x%x, pc=0x%x\n", start, pc);
		start = (IDATA) pc;

		/* Merge all branchTargets encountered */	
		if (bytecodeMap[pc] & BRANCH_TARGET) {
			if(x) printf("\ts22. bytecodeMap[%d](0x%x) & BRANCH_TARGET(0x%x)\n", pc, bytecodeMap[pc], BRANCH_TARGET);
			/* Don't try to merge a stack we just loaded */
			if (!justLoadedStack) {
				if(x) printf("\ts23. !justLoadedStack liveStack=%p, stackTop=%p\n", liveStack, stackTop);
				SAVE_STACKTOP(liveStack, stackTop);
				if(x) printf("\ts24. Before calling mergeStacks (verifyData(%p), start(0x%x))\n", verifyData, start);
				if (BCV_ERR_INSUFFICIENT_MEMORY == mergeStacks (verifyData, start)) {
					errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID;
					if(x) printf("\ts25. BCV_ERR_INSUFFICIENT_MEMORY=%d\n", BCV_ERR_INSUFFICIENT_MEMORY);
					goto _outOfMemoryError;
				}
				if(x) printf("\ts26. After calling mergeStacks, goto _checkFinished\n");
				goto _checkFinished;
			}
		}
		
		if(x) printf("\ts27. bcIndex=0x%x, code=0x%x, pc=0x%x bc=0x%x\n", bcIndex, code, pc, bc);
		justLoadedStack = FALSE;
		
		bcIndex = code + pc;
		bc = *bcIndex;
		if(x) printf("\ts28. bcIndex=0x%x, code=0x%x, pc=0x%x bc=0x%x\n", bcIndex, code, pc, bc);
#ifdef DEBUG_BCV
#if 1							/* for really verbose logging */
		printf("pc: %d bc: %d\n", pc, bc);
#endif
#endif
		if(x) {
			printf("\ts29. J9JavaInstructionSizeAndBranchActionTable=%p bc=0x%x J9JavaInstructionSizeAndBranchActionTable[%d]=0x%x pc=0x%x\n", 
			                J9JavaInstructionSizeAndBranchActionTable,   bc,                                              bc, J9JavaInstructionSizeAndBranchActionTable[bc], pc);
		}
		pc += (J9JavaInstructionSizeAndBranchActionTable[bc] & 7);
		if(x) printf("\ts30. pc=0x%x\n", pc);
		CHECK_END;
		
		if(x) printf("\ts31.JavaStackActionTable[%d]=0x%x popCount=0x%x\n", bc, JavaStackActionTable[bc], popCount);
		popCount = JavaStackActionTable[bc] & 0x07;
		if(x) printf("\ts32.popCount=0x%x\n", popCount);
		if ((stackTop - popCount) < stackBase) {
			if(x) printf("\ts33. (stackTop(%p) - popCount(0x%x)) < stackBase(%p)\n", stackTop, popCount, stackBase);
			errorType = J9NLS_BCV_ERR_STACK_UNDERFLOW__ID;
			verboseErrorCode = BCV_ERR_STACK_UNDERFLOW;
			/* Given that the actual data type involved has not yet been located through pop operation 
			 * when stack underflow occurs, it needs to step back by 1 slot to the actual data type 
			 * to be manipulated by the opcode.
			 */
			errorStackIndex = (U_32)(stackTop - liveStack->stackElements - 1);
			if(x) {
				printf("\ts34. errorType = J9NLS_BCV_ERR_STACK_UNDERFLOW__ID, verboseErrorCode = BCV_ERR_STACK_UNDERFLOW; errorStackIndex(0x%x) = (U_32)(stackTop(%p) - liveStack->stackElements(0x%x) - 1);\n",
				                                                                                                            errorStackIndex,            stackTop,           liveStack->stackElements);
			}
			/* Always set to the location of the 1st data type on 'stack' to show up if stackTop <= stackBase */
			if (stackTop <= stackBase) {
				if(x) printf("\ts35. stackTop(%p) <= stackBase(%p)\n", stackTop, stackBase);
				errorStackIndex = (U_32)(stackBase - liveStack->stackElements);
				if(x) printf("\ts36. errorStackIndex(0x%x) = (U_32)(stackBase(%p) - liveStack(%p)->stackElements(0x%x))", errorStackIndex, stackBase, liveStack, liveStack->stackElements);
			}
			if(x) printf("\ts37. goto _verifyError\n");
			goto _verifyError;
		}
		
		if(x) printf("\ts38. J9JavaBytecodeVerificationTable[%d]=0x%x type1=0x%x action=0x%x type2=0x%x decodeTable=%p\n", bc, J9JavaBytecodeVerificationTable[bc], type1, action, type2, decodeTable);
		type1 = (UDATA) J9JavaBytecodeVerificationTable[bc];
		action = type1 >> 8;
		type2 = (type1 >> 4) & 0xF;
		if(x) printf("\ts38. type1=0x%x action=0x%x type2=0x%x decodeTable=%p\n", type1, action, type2, decodeTable);
		type1 = (UDATA) decodeTable[type1 & 0xF];
		type2 = (UDATA) decodeTable[type2];
		if(x) printf("\ts39. type1=0x%x action=0x%x type2=0x%x decodeTable=%p\n", type1, action, type2, decodeTable);
		
		switch (action) {
		case RTV_NOP:
		case RTV_INCREMENT:
			break;

		case RTV_WIDE_LOAD_TEMP_PUSH:
			if(x) printf("\ts40. RTV_WIDE_LOAD_TEMP_PUSH\n");		
			if (type1 == BCV_GENERIC_OBJECT) {
				/* Only set for wide Objects - primitives don't read temps */
				wideIndex = TRUE;
				if(x) printf("\ts41.type1(0x%x) == BCV_GENERIC_OBJECT(0x%x)\n", type1, BCV_GENERIC_OBJECT);
			}	/* Fall through case !!! */
			
		case RTV_LOAD_TEMP_PUSH:
			if(x) printf("\ts42. RTV_LOAD_TEMP_PUSH\n");		
			if (type1 == BCV_GENERIC_OBJECT) {
				/* aload family */
				index = type2 & 0x7;
				if(x) printf("\ts43. type1(0x%x) == BCV_GENERIC_OBJECT(0x%x) index=0x%x type2=0x%x\n", type1, BCV_GENERIC_OBJECT, index, type2);
				if (type2 == 0) {
					index = PARAM_8(bcIndex, 1);
					if(x) printf("\ts44.index=0x%x bcIndex=0x%x wideIndex=%d\n", index, bcIndex, wideIndex);
					if (wideIndex) {
						index = PARAM_16(bcIndex, 1);
						wideIndex = FALSE;
						if(x) printf("\ts45.index=0x%x bcIndex=0x%x wideIndex=%d\n", index, bcIndex, wideIndex);
					}
				}
				type1 = temps[index];
				PUSH(type1);
				if(x) printf("\ts44.type1=0x%x\n", type1);
				break;
			}	/* Fall through case !!! */

		case RTV_PUSH_CONSTANT:
		_pushConstant:
			if(x) printf("\ts45. case RTV_PUSH_CONSTANT type1=0x%x\n", type1);
			PUSH(type1);
			if (type1 & BCV_WIDE_TYPE_MASK) {
				if(x) printf("\ts46. type1(0x%x) & BCV_WIDE_TYPE_MASK(0x%x) BCV_BASE_TYPE_TOP=0x%x\n", type1, BCV_WIDE_TYPE_MASK, BCV_BASE_TYPE_TOP);
				PUSH(BCV_BASE_TYPE_TOP);
			}
			break;

		case RTV_PUSH_CONSTANT_POOL_ITEM:
			if(x) printf("\ts47. case RTV_PUSH_CONSTANT_POOL_ITEM bc=0x%x verifyData=%p, romClass=%p, index=0x%x, stackTop=%p\n", bc, verifyData, romClass, index, stackTop);
			switch (bc) {
			case JBldc:
			case JBldcw:
				if(x) printf("\t\ts48.index=0x%x, bcIndex=0x%x\n", index, bcIndex);
				if (bc == JBldc) {
					index = PARAM_8(bcIndex, 1);
					if(x) printf("\t\ts49. case JBldc : index=0x%x, bcIndex=0x%x\n", index, bcIndex);
				} else {
					index = PARAM_16(bcIndex, 1);
					if(x) printf("\t\ts50. case JBldcw : index=0x%x, bcIndex=0x%x\n", index, bcIndex);
				}
				stackTop = pushLdcType(verifyData, romClass, index, stackTop);
				if(x) printf("\t\ts51. stacktop=%p, bc=0x%x, verifyData=%p, romClass=%p, index=0x%x, stackTop=%p\n", stackTop, bc, verifyData, romClass, index, stackTop);
				break;

			/* Change lookup table to generate constant of correct type */
			case JBldc2lw:
				if(x) printf("\t\ts52. case JBldc2lw\n");
				PUSH_LONG_CONSTANT;
				break;

			case JBldc2dw:
				if(x) printf("\t\ts53. case JBldc2dw\n");
				PUSH_DOUBLE_CONSTANT;
				break;
			}
			break;

		case RTV_ARRAY_FETCH_PUSH:
			if(x) printf("\ts54. case RTV_ARRAY_FETCH_PUSH\n");
			DROP(1);
			type = POP;
			if(x) printf("\ts55. type=0x%x\n", type);
			if (type != BCV_BASE_TYPE_NULL) {
				if(x) printf("\t\ts56. type(0x%x) != BCV_BASE_TYPE_NULL(0x%x)\n", type, BCV_BASE_TYPE_NULL);
				if (bc == JBaaload) {
					type1 = type - 0x01000000;	/* reduce types arity by one */
					PUSH(type1);
					if(x) printf("\t\ts57. type1=0x%x, type=0x%x\n", type1, type);
					break;
				}
			}
			if(x) printf("\ts56. goto _pushConstant\n");
			goto _pushConstant;
			break;

		case RTV_WIDE_POP_STORE_TEMP:
			if(x) printf("\ts57. case RTV_WIDE_POP_STORE_TEMP\n");
			wideIndex = TRUE;	/* Fall through case !!! */

		case RTV_POP_STORE_TEMP:
			if(x) printf("\ts58. case RTV_POP_STORE_TEMP index=0x%x, type2=0x%x\n", index, type2);
			index = type2 & 0x7;
			if(x) printf("\ts59. index=0x%x, type2=0x%x bcIndex=0x%x\n", index, type2, bcIndex);
			if (type2 == 0) {
				index = PARAM_8(bcIndex, 1);
				if(x) printf("\ts60. index=0x%x, type2=0x%x bcIndex=0x%x\n", index, type2, bcIndex);
				if (wideIndex) {
					index = PARAM_16(bcIndex, 1);
					wideIndex = FALSE;
					if(x) printf("\ts61. index=0x%x, type2=0x%x bcIndex=0x%x wideIndex = FALSE\n", index, type2, bcIndex);
				}
			}
			
			tempStoreChange = FALSE;
			if(x) printf("\ts62. type1=0x%x, BCV_GENERIC_OBJECT=0x%x\n", type1, BCV_GENERIC_OBJECT);
			
			if (type1 == BCV_GENERIC_OBJECT) {
				/* astore family */
				type = POP;
				tempStoreChange = (type != temps[index]);
				if(x) printf("\ts63. index=0x%x, type=0x%x, temps[%d]=0x%x\n", index, type, index, temps[index]);
				STORE_TEMP(index, type);
			} else {
				DROP(popCount);
				if(x) printf("\ts63. popCount=0x%x\n", popCount);
				/* because of pre-index local clearing - the order here matters */
				if (type1 & BCV_WIDE_TYPE_MASK) {
					if(x) printf("\ts64. type1(0x%x) & BCV_WIDE_TYPE_MASK(0x%x)\n", type1, BCV_WIDE_TYPE_MASK);
					tempStoreChange = (temps[index + 1] != BCV_BASE_TYPE_TOP);
					STORE_TEMP((index + 1), BCV_BASE_TYPE_TOP);
					if(x) printf("\ts65. tempStoreChange(0x%x) = (temps[%d](0x%x) != BCV_BASE_TYPE_TOP(0x%x)\n", tempStoreChange, index+1, temps[index + 1], BCV_BASE_TYPE_TOP);
				}
				tempStoreChange |= (type1 != temps[index]);
				STORE_TEMP(index, type1);
				if(x) printf("\ts66. tempStoreChange=0x%x, type1=0x%x, temps[%d]=0x%x, index=0x%x\n", tempStoreChange, type1, index, temps[index], index);
			}
			
			if (checkIfInsideException && tempStoreChange) {
				/* For all exception handlers covering this instruction */
				handler = J9EXCEPTIONINFO_HANDLERS(exceptionData);
				SAVE_STACKTOP(liveStack, stackTop);
				if(x) printf("\ts67. checkIfInsideException(0x%x) && tempStoreChange(0x%x) handler=%p exceptionData=%p\n", checkIfInsideException, tempStoreChange, handler, exceptionData);
				/* Save the current liveStack element zero */
				/* Reset the stack pointer to push the exception on the empty stack */
				originalStackTop = stackTop;
				originalStackZeroEntry = liveStack->stackElements[liveStack->stackBaseIndex];
				if(x) {
					printf("\ts68. originalStackTop=stackTop=%p originalStackZeroEntry(0x%x), liveStack(%p)->stackElements[%d]=0x%x\n", 
					                      stackTop,             originalStackZeroEntry,          liveStack,liveStack->stackBaseIndex,liveStack->stackElements[liveStack->stackBaseIndex]);
				}
				for (exception = 0; exception < (UDATA) exceptionData->catchCount; exception++) {
					if(x) printf("\ts69. exception=0x%x exceptionData=%p exceptionData->catchCount=0x%x\n", exception, exceptionData, exceptionData->catchCount);
					/* Find all matching exception ranges and copy/merge the stack with the exception object */
					if (((UDATA) start >= handler->startPC) && ((UDATA) start < handler->endPC)) {
#ifdef DEBUG_BCV
						printf("exception map change at startPC: %d\n", handler->startPC);
#endif
						if(x) printf("\ts70. start=0x%x, handler->startPC=0x%x, handler->endPC=0x%x, handler=%p\n", start, handler->startPC, handler->endPC, handler);
						stackIndex = bytecodeMap[handler->handlerPC] >> BRANCH_INDEX_SHIFT;
						branch = BCV_INDEX_STACK (stackIndex);
						/* "push" the exception object */
						classIndex = BCV_JAVA_LANG_THROWABLE_INDEX;
						if(x) printf("\ts71. stackIndex=0x%x, bytecodeMap[%d]=0x%x, BRANCH_INDEX_SHIFT=0x%x classIndex=0x%x\n", stackIndex, handler->handlerPC, bytecodeMap[handler->handlerPC], BRANCH_INDEX_SHIFT, classIndex);
						if (handler->exceptionClassIndex) {
							/* look up the class in the constant pool */
							utf8string = J9ROMSTRINGREF_UTF8DATA((J9ROMStringRef *) (&constantPool [handler->exceptionClassIndex]));
							classIndex = findClassName(verifyData, J9UTF8_DATA(utf8string), J9UTF8_LENGTH(utf8string));
							if(x) printf("\ts72. handler->exceptionClassIndex=0x%x utf8string=%p constantPool=%p handler=%p constantPool [%d]=0x%x\n", handler->exceptionClassIndex, utf8string, constantPool, handler, handler->exceptionClassIndex, constantPool [handler->exceptionClassIndex]);
						}

						/* Empty the stack */
						stackTop = &(liveStack->stackElements[liveStack->stackBaseIndex]);
						PUSH(classIndex << BCV_CLASS_INDEX_SHIFT);
						SAVE_STACKTOP(liveStack, stackTop);
						if(x) printf("\ts73. stackTop=%p liveStack=%p liveStack->stackElements[%d]=0x%x\n", stackTop, liveStack, liveStack->stackBaseIndex, liveStack->stackElements[liveStack->stackBaseIndex]);
						if (BCV_ERR_INSUFFICIENT_MEMORY == mergeStacks (verifyData, branch->pc)) {
							errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID;
							if(x) printf("\ts74. errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID = %d\n", errorType);
							goto _outOfMemoryError;
						}
					}
					handler++;
					if(x) printf("\ts75. handler=%p\n", handler);
				}

				/* Restore liveStack */
				liveStack->stackElements[liveStack->stackBaseIndex] = originalStackZeroEntry;
				stackTop = originalStackTop;
				if(x) printf("\ts76. liveStack=%p liveStack->stackElements[%d]=0x%x\n", liveStack, liveStack->stackBaseIndex, liveStack->stackElements[liveStack->stackBaseIndex]);
			}
			break;

		case RTV_POP_X_PUSH_X:
			popCount = 0;
			if(x) printf("\ts77. case RTV_POP_X_PUSH_X popCount = 0 type2=0x%x\n", type2);
			if (type2) {
				/* shift family */
				popCount = 1;
				if(x) printf("\ts77. case RTV_POP_X_PUSH_X popCount = 0x%x type2=0x%x\n", popCount, type2);
			}	/* fall through */
			
		case RTV_ARRAY_STORE:
			DROP(popCount);
			if(x) printf("\ts78. case RTV_ARRAY_STORE popCount=0x%x\n", popCount);
			break;

		case RTV_POP_X_PUSH_Y:
			if(x) printf("\ts79 case RTV_POP_X_PUSH_Y : type1=0x%x, type2=0x%x\n", type1, type2);
			/* Cause push of output type */
			type1 = type2;	/* fall through */

		case RTV_POP_2_PUSH:
			DROP(popCount);
			if(x) printf("\ts80. case RTV_POP_2_PUSH popCount=0x%x\n", popCount);
			goto _pushConstant;
			break;

		case RTV_BRANCH:
			popCount = type2 & 0x07;
			stackTop -= popCount;
			if(x) printf("\ts80. case RTV_BRANCH popCount=0x%x stackTop=%p\n", popCount, stackTop);
			if (bc == JBgotow) {
				offset32 = (I_32) PARAM_32(bcIndex, 1);
				target = start + offset32;
				if(x) printf("\ts81. bc == JBgotow(0x%x) offset32=0x%x bcIndex=0x%x start=0x%x target=0x%x\n", bc, offset32, bcIndex, start, target);
			} else {
				offset16 = (I_16) PARAM_16(bcIndex, 1);
				target = start + offset16;
				if(x) printf("\ts81. bc(0x%x) != JBgotow(0x%x) bcIndex=0x%x start=0x%x target=0x%x\n", bc, JBgotow, bcIndex, start, target);
			}

			SAVE_STACKTOP(liveStack, stackTop);
			/* Merge our stack to the target */
			if(x) printf("\ts82. Before calling mergeStacks(verifyData(%p), target(0x%x))\n", verifyData, target);
			if (BCV_ERR_INSUFFICIENT_MEMORY == mergeStacks (verifyData, target)) {
				errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID;
				if(x) printf("\ts83. errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID\n");
				goto _outOfMemoryError;
			}

			/* Unconditional branch (goto family) */
			if (popCount == 0) {
				if(x) printf("\ts84. popCount == 0\n");
				goto _checkFinished;
			}
			break;

		case RTV_RETURN:
			if(x) printf("\ts85. case RTV_RETURN\n");
			goto _checkFinished;
			break;

		case RTV_STATIC_FIELD_ACCESS:
			index = PARAM_16(bcIndex, 1);
			info = &constantPool[index];
			utf8string = ((J9UTF8 *) (J9ROMNAMEANDSIGNATURE_SIGNATURE(J9ROMFIELDREF_NAMEANDSIGNATURE((J9ROMFieldRef *) info))));
			if(x) printf("\ts86. index=0x%x, bcIndex=0x%x constantPool=%p constantPool[%d]=0x%x\n", index, bcIndex, constantPool, index, constantPool[index]);
			if (bc >= JBgetfield) {
				/* field bytecode receiver */
				DROP(1);
				if(x) printf("\ts87. bc(0x%x) >= JBgetfield(0x%x)\n", bc, JBgetfield);
			}
			
			if (bc & 1) {
				/* JBputfield/JBpustatic - odd bc's */
				if(x) printf("\ts88. bc=0x%x\n");
				DROP(1);
				if ((*J9UTF8_DATA(utf8string) == 'D') || (*J9UTF8_DATA(utf8string) == 'J')) {
					DROP(1);
					if(x) printf("\ts89. bc=0x%x utf8string=%p\n", utf8string);
				}
				
			} else {
				if(x) printf("\ts90. stackTop=%p, verifyData=%p, utf8string=%p\n", stackTop, verifyData, utf8string, stackTop);
				/* JBgetfield/JBgetstatic - even bc's */
				stackTop = pushFieldType(verifyData, utf8string, stackTop);
				if(x) printf("\ts91. stackTop=%p\n", stackTop);
			}
			break;

		case RTV_SEND:
			if(x) printf("\ts92. case RTV_SEND bc=0x%x\n", bc);
			if (bc == JBinvokeinterface2) {
				/* Set to point to JBinvokeinterface */
				bcIndex += 2;
				if(x) printf("\ts93. bc=0x%x bcIndex=0x%x\n", bc, bcIndex);
			}
			index = PARAM_16(bcIndex, 1);
			if(x) printf("\ts94. index=0x%x, bcIndex=0x%x\n", index, bcIndex);
			if (JBinvokestaticsplit == bc) {
				index = *(U_16 *)(J9ROMCLASS_STATICSPLITMETHODREFINDEXES(romClass) + index);
				if(x) printf("\ts95. JBinvokestaticsplit == bc == 0x%x romClass=%p index=0x%x\n", bc, romClass, index);
			} else if (JBinvokespecialsplit == bc) {
				index = *(U_16 *)(J9ROMCLASS_SPECIALSPLITMETHODREFINDEXES(romClass) + index);
				if(x) printf("\ts96. JBinvokespecialsplit == bc == 0x%x romClass=%p index=0x%x\n", bc, romClass, index);
			}
			if (bc == JBinvokedynamic) {
				/* TODO invokedynamic should allow for a 3 byte index.  Adjust 'index' to include the other byte */
				utf8string = ((J9UTF8 *) (J9ROMNAMEANDSIGNATURE_SIGNATURE(SRP_PTR_GET(callSiteData + index, J9ROMNameAndSignature*))));
				if(x) printf("\ts97. bc == JBinvokedynamic == 0x%x utf8string=%p callSiteData=%p index=0x%x\n", bc, utf8string, callSiteData, index);
			} else {
				info = &constantPool[index];
				utf8string = ((J9UTF8 *) (J9ROMNAMEANDSIGNATURE_SIGNATURE(J9ROMMETHODREF_NAMEANDSIGNATURE((J9ROMMethodRef *) info))));
				if(x) printf("\ts98. info=%p constantPool=%p constantPool[%d]=0x%x utf8string=%p\n", info, index, constantPool[index], utf8string);
			}
			stackTop -= getSendSlotsFromSignature(J9UTF8_DATA(utf8string));
			if(x) printf("\ts99. stackTop=%p utf8string=%p\n", stackTop, utf8string);
			
			if ((JBinvokestatic != bc) 
			&& (JBinvokedynamic != bc)
			&& (JBinvokestaticsplit != bc)
			) {
				if(x) printf("\ts100. bc=0x%x\n", bc);
				if ((JBinvokespecial == bc) 
				|| (JBinvokespecialsplit == bc)
				) {
					type = POP;
					if(x) printf("\ts101. bc=0x%x JBinvokespecial=0x%x JBinvokespecialsplit=0x%x type=0x%x\n", bc, JBinvokespecial, JBinvokespecialsplit, type);
					if (J9UTF8_DATA(J9ROMNAMEANDSIGNATURE_NAME(J9ROMMETHODREF_NAMEANDSIGNATURE((J9ROMMethodRef *) info)))[0] == '<') { 
						if(x) printf("\ts102.info=%p\n", info);
						/* This is <init>, verify that this is a NEW or INIT object */
						if (type & BCV_SPECIAL) {
							temp1 = getSpecialType(verifyData, type, code);
							/* This invoke special will make all copies of this "type" on the stack a real
							   object, find all copies of this object and initialize them */
							ptr = temps;	/* assumption that stack follows temps */
							/* we don't strictly need to walk temps here, the pending stack would be enough */
							while (ptr != stackTop) {
								if (*ptr == type) {
									*ptr = temp1;
								}
								ptr++;
							}
							type = temp1;
							break;
						}
					}
				} else { /* virtual or interface */
					DROP(1);
					if(x) printf("\ts103.\n");
				} 
			}
			if(x) printf("\ts104.verifyData=%p, utf8string=%p, stackTop=%p\n", verifyData, utf8string, stackTop);
			stackTop = pushReturnType(verifyData, utf8string, stackTop);
			if(x) printf("\ts105.verifyData=%p, utf8string=%p, stackTop=%p\n", verifyData, utf8string, stackTop);
			break;

		case RTV_PUSH_NEW:
			if(x) printf("\ts105. case RTV_PUSH_NEW : bc=0x%x\n", bc);
			switch (bc) {
			case JBnew:
			case JBnewdup:
				if(x) printf("\ts106. BCV_SPECIAL_NEW(0x%x) | (start(0x%x) << BCV_CLASS_INDEX_SHIFT(0x%x)) -> 0x%x\n", BCV_SPECIAL_NEW, start, BCV_CLASS_INDEX_SHIFT, (BCV_SPECIAL_NEW | (start << BCV_CLASS_INDEX_SHIFT)));
				/* put a uninitialized object of the correct type on the stack */
				PUSH(BCV_SPECIAL_NEW | (start << BCV_CLASS_INDEX_SHIFT));
				break;

			case JBnewarray:
				index = PARAM_8(bcIndex, 1);
				type = (UDATA) newArrayParamConversion[index];
				DROP(1);	/* pop the size of the array */
				PUSH(type);	/* arity of one implicit */
				if(x) printf("\ts107. index=0x%x, type=0x%x, newArrayParamConversion=%p\n", index, type, newArrayParamConversion);
				break;

			case JBanewarray:
				index = PARAM_16(bcIndex, 1);
				DROP(1);	/* pop the size of the array */
				info = &constantPool[index];
				utf8string = J9ROMSTRINGREF_UTF8DATA((J9ROMStringRef *) info);

				stackTop = pushClassType(verifyData, utf8string, stackTop);
				/* arity is one greater than signature */
				type = POP;
				PUSH(( (UDATA)1 << BCV_ARITY_SHIFT) + type);
				if(x) printf("\ts108. index=0x%x, bcIndex=0x%x, info=%p, constantPool=%p, type=0x%x, (( (UDATA)1 << BCV_ARITY_SHIFT) + type)=0x%x\n", index, bcIndex, info, constantPool, type, (( (UDATA)1 << BCV_ARITY_SHIFT) + type));
				break;

			case JBmultianewarray:
				/* points to cp entry for class of object to create */
				index = PARAM_16(bcIndex, 1);
				i1 = PARAM_8(bcIndex, 3);
				DROP(i1);
				if(x) printf("\ts109. index=0x%x, bcIndex=0x%x i1=0x%x stackTop=%p, stackBase=%p\n", index, bcIndex, i1, stackTop, stackBase);
				if (stackTop < stackBase) {
					errorType = J9NLS_BCV_ERR_STACK_UNDERFLOW__ID;
					verboseErrorCode = BCV_ERR_STACK_UNDERFLOW;
					/* Always set to the location of the 1st data type on 'stack' to show up if stackTop <= stackBase */
					errorStackIndex = (U_32)(stackBase - liveStack->stackElements);
					if(x) printf("\ts110\n");
					goto _verifyError;
				}

				info = &constantPool[index];
				utf8string = J9ROMSTRINGREF_UTF8DATA((J9ROMStringRef *) info);
				if(x) printf("\ts111. info=%p, constantPool=%p, constantPool[%d]=0x%x verifyData=%p, utf8string=%p, stackTop=%p\n", info, constantPool, index, constantPool[index], verifyData, utf8string, stackTop);
				stackTop = pushClassType(verifyData, utf8string, stackTop);
				if(x) printf("\ts112. stackTop=%p\n", stackTop);
				break;
			}
			if(x) printf("\ts113.\n");
			break;

		case RTV_MISC:
			if(x) printf("\ts114. case RTV_MISC. bc=0x%x\n", bc);
			switch (bc) {
			case JBathrow:
				if(x) printf("\t\ts115 JBathrow=0x%x\n", JBathrow);
				goto _checkFinished;
				break;

			case JBarraylength:
			case JBinstanceof:
				DROP(1);
				PUSH_INTEGER_CONSTANT;
				if(x) printf("\t\ts116 JBinstanceof=0x%x\n", JBinstanceof);
				break;

			case JBtableswitch:
			case JBlookupswitch:
				if(x) printf("\t\ts117. pc=0x%x, index=0x%x, bcIndex=0x%x, start=0x%x liveStack=%p, stackTop=%p\n", pc, index, bcIndex, start, liveStack, stackTop);
				DROP(1);
				index = (UDATA) ((4 - (pc & 3)) & 3);	/* consume padding */
				pc += index;
				bcIndex += index;
				pc += 8;
				if(x) printf("\t\ts117.5 pc=0x%x, index=0x%x, bcIndex=0x%x, start=0x%x liveStack=%p, stackTop=%p\n", pc, index, bcIndex, start, liveStack, stackTop);
				CHECK_END;
				offset32 = (I_32) PARAM_32(bcIndex, 1);
				bcIndex += 4;
				target = offset32 + start;
				if(x) printf("\t\ts118. pc=0x%x, index=0x%x, bcIndex=0x%x, start=0x%x liveStack=%p, stackTop=%p offset32=0x%x\n", pc, index, bcIndex, start, liveStack, stackTop, offset32);
				SAVE_STACKTOP(liveStack, stackTop);
				if(x) printf("\t\ts119. Before calling mergeStack() verifyData=%p, target=0x%x\n",verifyData, target);
				if (BCV_ERR_INSUFFICIENT_MEMORY == mergeStacks (verifyData, target)) {
					errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID;
					if(x) printf("\t\ts120.\n");
					goto _outOfMemoryError;
				}

				if (bc == JBtableswitch) {
					if(x) printf("\t\ts121. i1=0x%x i2=0x%x, bcIndex=0x%x, pc=0x%x\n", i1, i2, bcIndex, pc);
					i1 = (I_32) PARAM_32(bcIndex, 1);
					bcIndex += 4;
					pc += 4;
					i2 = (I_32) PARAM_32(bcIndex, 1);
					bcIndex += 4;

					pc += ((I_32)i2 - (I_32)i1 + 1) * 4;
					if(x) printf("\t\ts121.5 i1=0x%x i2=0x%x, bcIndex=0x%x, pc=0x%x\n", i1, i2, bcIndex, pc);
					CHECK_END;

					/* Add the table switch destinations in reverse order to more closely mimic the order that people
					   (ie: the TCKs) expect you to load classes */
					bcIndex += (((I_32)i2 - (I_32)i1) * 4);	/* point at the last table switch entry */

					/* Count the entries */
					i2 = (I_32)i2 - (I_32)i1 + 1;
					if(x) printf("\t\ts122. i1=0x%x i2=0x%x, bcIndex=0x%x, pc=0x%x\n", i1, i2, bcIndex, pc);
					for (i1 = 0; (I_32)i1 < (I_32)i2; i1++) {
						if(x) printf("\t\ts123. i1=0x%x, i2=0x%x\n", i1,i2);
						offset32 = (I_32) PARAM_32(bcIndex, 1);
						bcIndex -= 4;	/* back up to point at the previous table switch entry */
						target = offset32 + start;
						if(x) printf("\t\ts124. offset32=0x%x, bcIndex=0x%x, start=0x%x, target=0x%x\n", offset32, bcIndex, start, target);
						if (BCV_ERR_INSUFFICIENT_MEMORY == mergeStacks (verifyData, target)) {
							errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID;
							if(x) printf("\t\ts125.\n");
							goto _outOfMemoryError;
						}
					}
				} else {
					if(x) printf("\t\ts126. i2=0x%x, bcIndex=0x%x\n", i2, bcIndex);
					i2 = (I_32) PARAM_32(bcIndex, 1);
					bcIndex += 4;

					pc += (I_32)i2 * 8;
					if(x) printf("\t\ts126. i2=0x%x, bcIndex=0x%x pc=0x%x\n", i2, bcIndex, pc);
					CHECK_END;
					if(x) printf("\t\ts126.5. i2=0x%x, bcIndex=0x%x pc=0x%x\n", i2, bcIndex, pc);
					for (i1 = 0; (I_32)i1 < (I_32)i2; i1++) {
						if(x) printf("\t\ts127. i1=0x%x, i2=0x%x bcIndex=0x%x, start=0x%x\n", i1, i2, bcIndex, start);
						bcIndex += 4;
						offset32 = (I_32) PARAM_32(bcIndex, 1);
						bcIndex += 4;
						target = offset32 + start;
						if(x) printf("\t\ts128. i1=0x%x, i2=0x%x bcIndex=0x%x, start=0x%x offset32=0x%x target=0x%x\n", i1, i2, bcIndex, start, offset32, target);
						
						if (BCV_ERR_INSUFFICIENT_MEMORY == mergeStacks (verifyData, target)) {
							errorType = J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID;
							if(x) printf("\t\ts129. J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID=%d\n", J9NLS_BCV_ERR_VERIFY_OUT_OF_MEMORY__ID);
							goto _outOfMemoryError;
						}
					}
				}
				if(x) printf("\t\ts130. goto _checkFinished;\n");
				goto _checkFinished;
				break;

			case JBmonitorenter:
			case JBmonitorexit:
				DROP(1);
				if(x) printf("\t\ts131. JBmonitorenter=0x%x, JBmonitorexit=0x%x\n", JBmonitorenter, JBmonitorexit);
				break;

			case JBcheckcast:
				if(x) printf("\t\ts132. case JBcheckcast index=0x%x, bcIndex=0x%x constantPool=%p info=%p verifyData=%p, stackTop=%p\n", index, bcIndex, constantPool, info, verifyData, stackTop);
				index = PARAM_16(bcIndex, 1);
				DROP(1);
				info = &constantPool[index];
				utf8string = J9ROMSTRINGREF_UTF8DATA((J9ROMStringRef *) info);
				stackTop = pushClassType(verifyData, utf8string, stackTop);
				if(x) printf("\t\ts133. index=0x%x, bcIndex=0x%x constantPool=%p info=%p verifyData=%p, utf8string=%p, stackTop=%p\n", index, bcIndex, constantPool, info, verifyData, utf8string, stackTop);
				break;
			}
			break;

		case RTV_POP_2_PUSH_INT:
			DROP(popCount);
			PUSH_INTEGER_CONSTANT;
			if(x) printf("\ts134. popCount=0x%x\n", popCount);
			break;

		case RTV_BYTECODE_POP:
		case RTV_BYTECODE_POP2:
			DROP(popCount);
			if(x) printf("\ts135. popCount=0x%x\n", popCount);
			break;

		case RTV_BYTECODE_DUP:
			type = POP;
			PUSH(type);
			PUSH(type);
			if(x) printf("\ts136. popCount=0x%x type=0x%x\n", popCount, type);
			break;

		case RTV_BYTECODE_DUPX1:
			type = POP;
			temp1 = POP;
			PUSH(type);
			PUSH(temp1);
			PUSH(type);
			if(x) printf("\ts137. type=0x%x temp1=0x%x\n", type, temp1);
			break;

		case RTV_BYTECODE_DUPX2:
			type = POP;
			temp1 = POP;
			temp2 = POP;
			PUSH(type);
			PUSH(temp2);
			PUSH(temp1);
			PUSH(type);
			if(x) printf("\ts138. type=0x%x temp1=0x%x temp2=0x%x\n", type, temp1, temp2);
			break;

		case RTV_BYTECODE_DUP2:
			temp1 = POP;
			temp2 = POP;
			PUSH(temp2);
			PUSH(temp1);
			PUSH(temp2);
			PUSH(temp1);
			if(x) printf("\ts139. temp1=0x%x temp2=0x%x\n", temp1, temp2);
			break;

		case RTV_BYTECODE_DUP2X1:
			type = POP;
			temp1 = POP;
			temp2 = POP;
			PUSH(temp1);
			PUSH(type);
			PUSH(temp2);
			PUSH(temp1);
			PUSH(type);
			if(x) printf("\ts140. type=0x%x temp1=0x%x temp2=0x%x\n", type, temp1, temp2);
			break;

		case RTV_BYTECODE_DUP2X2:
			type = POP;
			temp1 = POP;
			temp2 = POP;
			temp3 = POP;
			PUSH(temp1);
			PUSH(type);
			PUSH(temp3);
			PUSH(temp2);
			PUSH(temp1);
			PUSH(type);
			if(x) printf("\ts141. type=0x%x temp1=0x%x temp2=0x%x temp3=0x%x\n", type, temp1, temp2, temp3);
			break;

		case RTV_BYTECODE_SWAP:
			type = POP;
			temp1 = POP;
			PUSH(type);
			PUSH(temp1);
			if(x) printf("\ts142. type=0x%x temp1=0x%x\n", type, temp1);
			break;

		case RTV_UNIMPLEMENTED:
			errorType = J9NLS_BCV_ERR_BC_UNKNOWN__ID;
			/* Jazz 104084: Set the error code in the case of unrecognized opcode. */
			verboseErrorCode = BCV_ERR_BAD_BYTECODE;
			if(x) printf("\ts143. goto _verifyError\n");
			goto _verifyError;
			break;
		}
		if(x) printf("\ts144. Before continue\n");
		continue;

_checkFinished:
		if(x) printf("\ts145. _checkFinished verifyData=%p verifyData->unwalkedQueueHead=%p, verifyData->unwalkedQueueTail=%p\n", verifyData, verifyData->unwalkedQueueHead, verifyData->unwalkedQueueTail);
		if (verifyData->unwalkedQueueHead != verifyData->unwalkedQueueTail) {
			pc = verifyData->unwalkedQueue[verifyData->unwalkedQueueHead++];
			verifyData->unwalkedQueueHead %= (verifyData->rootQueueSize / sizeof(UDATA));
			if(x) printf("\ts146. pc=0x%x verifyData=%p verifyData->unwalkedQueueHead=%p, verifyData->unwalkedQueueTail=%p\n", pc, verifyData, verifyData->unwalkedQueueHead, verifyData->unwalkedQueueTail);
			if ((bytecodeMap[pc] & BRANCH_ON_UNWALKED_QUEUE) == 0) {
				if(x) printf("\ts147. (bytecodeMap[%d](0x%x) & BRANCH_ON_UNWALKED_QUEUE(0x%x)) == 0, goto _checkFinished;\n", pc, bytecodeMap[pc], BRANCH_ON_UNWALKED_QUEUE);
				goto _checkFinished;
			}
			bytecodeMap[pc] &= ~BRANCH_ON_UNWALKED_QUEUE;
			bcIndex = code + pc;
			stackIndex = bytecodeMap[pc] >> BRANCH_INDEX_SHIFT;
			branch = BCV_INDEX_STACK (stackIndex);
			copyStack(branch, liveStack);
			if(x) printf("\ts147. bytecodeMap[%d]=0x%x bcIndex=0x%x code=0x%x pc=0x%x stackIndex=0x%x branch=%p, liveStack=%p\n", pc, bytecodeMap[pc], bcIndex, code, pc, stackIndex, branch, liveStack);
			RELOAD_LIVESTACK;
			justLoadedStack = TRUE;
			Trc_BCV_simulateStack_NewWalkFrom(verifyData->vmStruct, 
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
					start, start, pc, pc);
			if(x) printf("\ts148. branch=%p, liveStack=%p\n", branch, liveStack);
		} else if (verifyData->rewalkQueueHead != verifyData->rewalkQueueTail) {
			if(x) printf("\ts149. verifyData->rewalkQueueHead(0x%x) != verifyData->rewalkQueueTail(0x%x)\n", verifyData->rewalkQueueHead, verifyData->rewalkQueueTail);
			pc = verifyData->rewalkQueue[verifyData->rewalkQueueHead++];
			verifyData->rewalkQueueHead %= (verifyData->rootQueueSize / sizeof(UDATA));
			if(x) printf("\ts150. pc=0x%x verifyData->rewalkQueueHead=0x%x\n", pc, verifyData->rewalkQueueHead);
			if ((bytecodeMap[pc] & BRANCH_ON_REWALK_QUEUE) == 0) {
				if(x) printf("\ts151. (bytecodeMap[%d](0x%x) & BRANCH_ON_REWALK_QUEUE(0x%x)) == 0\n", pc, bytecodeMap[pc], BRANCH_ON_REWALK_QUEUE);
				goto _checkFinished;
			}
			bytecodeMap[pc] &= ~BRANCH_ON_REWALK_QUEUE;
			bcIndex = code + pc;
			stackIndex = bytecodeMap[pc] >> BRANCH_INDEX_SHIFT;
			branch = BCV_INDEX_STACK (stackIndex);
			copyStack(branch, liveStack);
			if(x) printf("\ts152. bytecodeMap[%d]=0x%x, bcIndex=0x%x, code=0x%x, pc=0x%x, stackIndex=0x%x, branch=%p, liveStack\n", pc, bytecodeMap[pc], bcIndex, code, pc, stackIndex, branch, liveStack);
			RELOAD_LIVESTACK;
			justLoadedStack = TRUE;
			Trc_BCV_simulateStack_RewalkFrom(verifyData->vmStruct, 
					(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
					(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
					J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
					start, start, pc, pc);
			if(x) printf("\ts153. start=0x%x, pc=0x%x\n", start, pc);
		} else {
			Trc_BCV_simulateStack_Exit(verifyData->vmStruct);
			/* else we are done the rootSet -- return */
			if(x) printf("\ts154. return BCV_SUCCESS\n");
			return BCV_SUCCESS;
		}
	}
#undef CHECK_END

	errorType = J9NLS_BCV_ERR_UNEXPECTED_EOF__ID;	/* should never reach here */
	if(x) printf("\ts155.\n");
_verifyError:
	/* Jazz 104084: Store the verification error data here when error occurs */
	storeVerifyErrorData(verifyData, (I_16)verboseErrorCode, (U_32)errorStackIndex, errorTargetType, errorTempData, start);

	BUILD_VERIFY_ERROR(errorModule, errorType);
	Trc_BCV_simulateStack_verifyError(verifyData->vmStruct,
										verifyData->errorPC,
										verifyData->errorCode);
	Trc_BCV_simulateStack_verifyErrorBytecode(verifyData->vmStruct,
			(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
			(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
			J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
			verifyData->errorCode, verifyData->errorPC, verifyData->errorPC, bc);
	Trc_BCV_simulateStack_Exit(verifyData->vmStruct);
	if(x) printf("\ts156. verifyData->errorCode=0x%x, verifyData->errorPC=0x%x, verifyData->errorPC=0x%x, bc=0x%x return BCV_ERR_INTERNAL_ERROR\n", verifyData->errorCode, verifyData->errorPC, verifyData->errorPC, bc);
	return BCV_ERR_INTERNAL_ERROR;

_outOfMemoryError:
	BUILD_VERIFY_ERROR(errorModule, errorType);
	Trc_BCV_simulateStack_verifyError(verifyData->vmStruct,
										verifyData->errorPC,
										verifyData->errorCode);

	Trc_BCV_simulateStack_verifyErrorBytecode_OutOfMemoryException(verifyData->vmStruct,
		(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
		J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
		(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
		J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
		(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
		J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
		verifyData->errorCode, verifyData->errorPC, verifyData->errorPC, bc);
	Trc_BCV_simulateStack_Exit(verifyData->vmStruct);
	if(x) printf("\ts157. verifyData->errorCode=0x%x, verifyData->errorPC=0x%x, verifyData->errorPC=0x%x, bc=0x%x return BCV_ERR_INSUFFICIENT_MEMORY\n", verifyData->errorCode, verifyData->errorPC, verifyData->errorPC, bc);
	return BCV_ERR_INSUFFICIENT_MEMORY;

}

/*
 * return BCV_SUCCESS on success
 * returns BCV_ERR_INSUFFICIENT_MEMORY on OOM
 */

IDATA
allocateVerifyBuffers (J9PortLibrary * portLib, J9BytecodeVerificationData *verifyData)
{
	Trc_BCV_allocateVerifyBuffers_Event1(verifyData->vmStruct);

	verifyData->classNameList = 0;
	verifyData->classNameListEnd = 0;
	verifyData->classNameSegment = 0;
	verifyData->classNameSegmentFree = 0;
	verifyData->classNameSegmentEnd = 0;
	verifyData->bytecodeMap = 0;
	verifyData->stackMaps = 0;
	verifyData->liveStack = 0;
	verifyData->unwalkedQueue = 0;
	verifyData->rewalkQueue = 0;

	verifyData->classNameList = (J9UTF8 **) bcvalloc (verifyData, (UDATA) CLASSNAMELIST_DEFAULT_SIZE);
	verifyData->classNameListEnd = (J9UTF8 **)((UDATA)verifyData->classNameList + CLASSNAMELIST_DEFAULT_SIZE);

	verifyData->classNameSegment = bcvalloc (verifyData, (UDATA) CLASSNAMESEGMENT_DEFAULT_SIZE);
	verifyData->classNameSegmentEnd = verifyData->classNameSegment + CLASSNAMESEGMENT_DEFAULT_SIZE;
	verifyData->classNameSegmentFree = verifyData->classNameSegment;

	verifyData->bytecodeMap = bcvalloc (verifyData, (UDATA) BYTECODE_MAP_DEFAULT_SIZE);
	verifyData->bytecodeMapSize = BYTECODE_MAP_DEFAULT_SIZE;

	verifyData->stackMaps = bcvalloc (verifyData, (UDATA) STACK_MAPS_DEFAULT_SIZE);
	verifyData->stackMapsSize = STACK_MAPS_DEFAULT_SIZE;
	verifyData->stackMapsCount = 0;

	verifyData->unwalkedQueue = bcvalloc (verifyData, (UDATA) ROOT_QUEUE_DEFAULT_SIZE);
	verifyData->unwalkedQueueHead = 0;
	verifyData->unwalkedQueueTail = 0;
	verifyData->rewalkQueue = bcvalloc (verifyData, (UDATA) ROOT_QUEUE_DEFAULT_SIZE);
	verifyData->rewalkQueueHead = 0;
	verifyData->rewalkQueueTail = 0;
	verifyData->rootQueueSize = ROOT_QUEUE_DEFAULT_SIZE;

	verifyData->liveStack = bcvalloc (verifyData, (UDATA) LIVE_STACK_DEFAULT_SIZE);
	verifyData->liveStackSize = LIVE_STACK_DEFAULT_SIZE;
	verifyData->stackSize = 0;

	RESET_VERIFY_ERROR(verifyData);

	verifyData->portLib = portLib;

	if (!(verifyData->classNameList && verifyData->classNameSegment && verifyData->bytecodeMap 
			&& verifyData->stackMaps && verifyData->unwalkedQueue && verifyData->rewalkQueue && verifyData->liveStack)) {
		freeVerifyBuffers (portLib, verifyData);
		Trc_BCV_allocateVerifyBuffers_allocFailure(verifyData->vmStruct);
		return BCV_ERR_INSUFFICIENT_MEMORY;
	}
	/* Now we know the allocates were successful, initialize the required data */
	verifyData->classNameList[0] = NULL;
	return BCV_SUCCESS;
}


/*
	BCV interface to j9mem_allocate_memory.
	@return pointer to allocated memory, or 0 if allocation fails.
	@note Does not deallocate the internal buffer
*/

void*  
bcvalloc (J9BytecodeVerificationData * verifyData, UDATA byteCount)
{
	UDATA *returnVal = 0;
	J9BCVAlloc *temp1, *temp2;

	PORT_ACCESS_FROM_PORT(verifyData->portLib);

	/* Round to UDATA multiple */
	byteCount = (UDATA) ((byteCount + (sizeof(UDATA) - 1)) & ~(sizeof(UDATA) - 1));
	/* Allow room for the linking header */
	byteCount += sizeof(UDATA);

	if (verifyData->internalBufferStart == 0) {
		verifyData->internalBufferStart = j9mem_allocate_memory(BCV_INTERNAL_DEFAULT_SIZE, J9MEM_CATEGORY_CLASSES);
		if (verifyData->internalBufferStart == 0) {
			return 0;
		}
		verifyData->internalBufferEnd = (UDATA *) ((UDATA)verifyData->internalBufferStart + BCV_INTERNAL_DEFAULT_SIZE);
		verifyData->currentAlloc = verifyData->internalBufferStart;
		*verifyData->currentAlloc = (UDATA) verifyData->currentAlloc;
	}

	temp1 = (J9BCVAlloc *) verifyData->currentAlloc;
	temp2 = (J9BCVAlloc *) ((UDATA) temp1 + byteCount);

	if ((UDATA *) temp2 >= verifyData->internalBufferEnd) {
		returnVal = j9mem_allocate_memory(byteCount, J9MEM_CATEGORY_CLASSES);
		Trc_BCV_bcvalloc_ExternalAlloc(verifyData->vmStruct, 
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				byteCount, returnVal);
		if (returnVal == 0) {
			return 0;
		}
	} else {
		/* tag the back pointer as the block following this pointer is in use */
		temp1->prev = (J9BCVAlloc *) ((UDATA) temp1->prev | 1);
		temp2->prev = temp1;
		verifyData->currentAlloc = (UDATA *) temp2;
		returnVal = temp1->data;
	}
	return returnVal;
}



/*
	BCV interface to j9mem_allocate_memory.
*/

void  
bcvfree (J9BytecodeVerificationData * verifyData, void* address)
{
	J9BCVAlloc *temp1, *temp2;

	PORT_ACCESS_FROM_PORT(verifyData->portLib);

	if (((UDATA *) address >= verifyData->internalBufferEnd) || ((UDATA *) address < verifyData->internalBufferStart)) {
		Trc_BCV_bcvalloc_ExternalFreeAddress(verifyData->vmStruct, address);
		j9mem_free_memory(address);
		return;
	}

	temp1 = (J9BCVAlloc *) ((UDATA *) address - 1);
	/* flag block following the pointer as free */
	temp1->prev = (J9BCVAlloc *) ((UDATA) temp1->prev & ~1);
	temp2 = (J9BCVAlloc *) verifyData->currentAlloc;

	while (temp1 == temp2->prev) {
		/* Release most recent alloc and any preceding contiguous already freed allocs */
		temp2 = temp2->prev;
		temp1 = temp2->prev;
		if ((UDATA) temp1->prev & 1) {
			/* stop if an in-use block is found */
			verifyData->currentAlloc = (UDATA *) temp2;
			break;
		}
		if (temp1 == temp2) {
			/* all blocks unused - release the buffer */
			j9mem_free_memory(verifyData->internalBufferStart);
			verifyData->internalBufferStart = 0;	/* Set the internal buffer start to zero so it will be re-allocated next time */
			verifyData->internalBufferEnd = 0;
			break;
		}
	}
}


void  
freeVerifyBuffers (J9PortLibrary * portLib, J9BytecodeVerificationData *verifyData)
{
	Trc_BCV_freeVerifyBuffers_Event1(verifyData->vmStruct);

	if (verifyData->classNameList ) {
		bcvfree (verifyData, verifyData->classNameList);
	}

	if (verifyData->classNameSegment ) {
		bcvfree (verifyData, verifyData->classNameSegment);
	}

	if (verifyData->bytecodeMap ) {
		bcvfree (verifyData, verifyData->bytecodeMap);
	}

	if (verifyData->stackMaps ) {
		bcvfree (verifyData, verifyData->stackMaps);
	}

	if (verifyData->unwalkedQueue ) {
		bcvfree (verifyData, verifyData->unwalkedQueue);
	}

	if (verifyData->rewalkQueue ) {
		bcvfree (verifyData, verifyData->rewalkQueue);
	}

	if (verifyData->liveStack ) {
		bcvfree (verifyData, verifyData->liveStack);
	}

	verifyData->classNameList = 0;
	verifyData->classNameListEnd = 0;
	verifyData->classNameSegment = 0;
	verifyData->classNameSegmentFree = 0;
	verifyData->classNameSegmentEnd = 0;
	verifyData->bytecodeMap = 0;
	verifyData->stackMaps = 0;
	verifyData->liveStack = 0;
	verifyData->unwalkedQueue = 0;
	verifyData->rewalkQueue = 0;
}



void  
j9bcv_freeVerificationData (J9PortLibrary * portLib, J9BytecodeVerificationData * verifyData)
{
	PORT_ACCESS_FROM_PORT(portLib);
	if (verifyData) {
#ifdef J9VM_THR_PREEMPTIVE
		JavaVM* jniVM = (JavaVM*)verifyData->javaVM;
	    J9ThreadEnv* threadEnv;
		(*jniVM)->GetEnv(jniVM, (void**)&threadEnv, J9THREAD_VERSION_1_1);

		threadEnv->monitor_destroy( verifyData->verifierMutex );
#endif
		freeVerifyBuffers( PORTLIB, verifyData );
		j9mem_free_memory( verifyData->excludeAttribute );
		j9mem_free_memory( verifyData );
	}
}

/*
 * returns J9BytecodeVerificationData* on success
 * returns NULL on OOM
 */
J9BytecodeVerificationData *  
j9bcv_initializeVerificationData(J9JavaVM* javaVM)
{
	J9BytecodeVerificationData * verifyData;
	PORT_ACCESS_FROM_JAVAVM(javaVM);
	JavaVM* jniVM = (JavaVM*)javaVM;
	J9ThreadEnv* threadEnv;

	(*jniVM)->GetEnv(jniVM, (void**)&threadEnv, J9THREAD_VERSION_1_1);

	verifyData = j9mem_allocate_memory((UDATA) sizeof(*verifyData), J9MEM_CATEGORY_CLASSES);
	if( !verifyData ) {
		goto error_no_memory;
	}

	/* blank the vmStruct field */
	verifyData->vmStruct = NULL;
	verifyData->javaVM = javaVM;

#ifdef J9VM_THR_PREEMPTIVE
	threadEnv->monitor_init_with_name(&verifyData->verifierMutex, 0, "BCVD verifier");
	if (!verifyData->verifierMutex) {
		goto error_no_memory;
	}
#endif

	verifyData->verifyBytecodesFunction = j9bcv_verifyBytecodes;
	verifyData->checkClassLoadingConstraintForNameFunction = j9bcv_checkClassLoadingConstraintForName;
	verifyData->internalBufferStart = 0;
	verifyData->internalBufferEnd = 0;
	verifyData->portLib = PORTLIB;
	verifyData->ignoreStackMaps = 0;
	verifyData->excludeAttribute = NULL;
	verifyData->redefinedClassesCount = 0;
	if (BCV_ERR_INSUFFICIENT_MEMORY == allocateVerifyBuffers (PORTLIB, verifyData)) {
		goto error_no_memory;
	}

	/* default verification options */
	verifyData->verificationFlags = J9_VERIFY_SKIP_BOOTSTRAP_CLASSES | J9_VERIFY_OPTIMIZE; 	

	return verifyData;

error_no_memory:
	if (verifyData) {
#ifdef J9VM_THR_PREEMPTIVE
		threadEnv->monitor_destroy (verifyData->verifierMutex);
#endif
		j9mem_free_memory(verifyData);
	}
	return NULL;
}



#define ALLOC_BUFFER(name, needed) \
	if (needed > name##Size) { \
		bcvfree(verifyData, name); \
		name = bcvalloc(verifyData, needed); \
		if (NULL == name) { \
			name##Size = 0; \
			result = BCV_ERR_INSUFFICIENT_MEMORY; \
			break; \
		} \
		name##Size = needed; \
	}

/* 
 * Sequence the 2 verification passes - flow based type inference stack map generation
 * and linear stack map verification
 *
 * returns BCV_SUCCESS on success
 * returns BCV_ERR_INSUFFICIENT_MEMORY on OOM
 */

IDATA 
j9bcv_verifyBytecodes (J9PortLibrary * portLib, J9Class * clazz, J9ROMClass * romClass,
		   J9BytecodeVerificationData * verifyData)
{
	UDATA i, j;
	J9ROMMethod *romMethod;
	UDATA argCount;
	UDATA length;
	UDATA mapLength;
	BOOLEAN hasStackMaps = (J9ROMCLASS_HAS_VERIFY_DATA(romClass) != 0);
	UDATA oldState;
	IDATA result = 0;
	UDATA rootQueueSize;
	U_32 *bytecodeMap;
	UDATA start = 0;
	J9BranchTargetStack *liveStack;
	U_8 *stackMapData;
	UDATA stackMapsSize;
	UDATA *stackTop;
	UDATA x = 0;
	BOOLEAN classVersionRequiresStackmaps = romClass->majorVersion >= CFR_MAJOR_VERSION_REQUIRING_STACKMAPS;
	BOOLEAN newFormat = (classVersionRequiresStackmaps || hasStackMaps);
	BOOLEAN verboseVerification = (J9_VERIFY_VERBOSE_VERIFICATION == (verifyData->verificationFlags & J9_VERIFY_VERBOSE_VERIFICATION));

	PORT_ACCESS_FROM_PORT(portLib);
	Trc_BCV_j9bcv_verifyBytecodes_Entry(verifyData->vmStruct,
									(UDATA) J9UTF8_LENGTH((J9ROMCLASS_CLASSNAME(romClass))),
									J9UTF8_DATA(J9ROMCLASS_CLASSNAME(romClass)));

	/* save current and set vmState */
	oldState = verifyData->vmStruct->omrVMThread->vmState;
	verifyData->vmStruct->omrVMThread->vmState = J9VMSTATE_BCVERIFY;

	verifyData->romClass = romClass;
	verifyData->errorPC = 0;
	
	verifyData->romClassInSharedClasses = j9shr_Query_IsAddressInCache(verifyData->javaVM, romClass, romClass->romSize);

	/* List is used for the whole class */
	initializeClassNameList(verifyData);


	romMethod = (J9ROMMethod *) J9ROMCLASS_ROMMETHODS(romClass);

	if (verboseVerification) {
		ALWAYS_TRIGGER_J9HOOK_VM_CLASS_VERIFICATION_START(verifyData->javaVM->hookInterface, verifyData, newFormat);
	}

	/* For each method in the class */
	for (i = 0; i < (UDATA) romClass->romMethodCount; i++) {

		UDATA createStackMaps;
		
		verifyData->ignoreStackMaps = (verifyData->verificationFlags & J9_VERIFY_IGNORE_STACK_MAPS) != 0;
		verifyData->createdStackMap = FALSE;
		verifyData->romMethod = romMethod;

		Trc_BCV_j9bcv_verifyBytecodes_VerifyMethod(verifyData->vmStruct,
				(UDATA) J9UTF8_LENGTH((J9ROMCLASS_CLASSNAME(romClass))),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(romClass)),
				(UDATA) J9UTF8_LENGTH((J9ROMMETHOD_NAME(romMethod))),
				J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
				(UDATA) J9UTF8_LENGTH((J9ROMMETHOD_SIGNATURE(romMethod))),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)),
				romMethod->modifiers);

		/* If native or abstract method, do nothing */
		if (!((romMethod->modifiers & J9AccNative) || (romMethod->modifiers & J9AccAbstract))) {
			BOOLEAN isInitMethod = FALSE;

			/* BCV_TARGET_STACK_HEADER_UDATA_SIZE for pc/stackBase/stackEnd in J9BranchTargetStack and
			 * BCV_STACK_OVERFLOW_BUFFER_UDATA_SIZE for late overflow detection of longs/doubles
			 */
			verifyData->stackSize = (J9_MAX_STACK_FROM_ROM_METHOD(romMethod)
									+ J9_ARG_COUNT_FROM_ROM_METHOD(romMethod)
									+ J9_TEMP_COUNT_FROM_ROM_METHOD(romMethod)
									+ BCV_TARGET_STACK_HEADER_UDATA_SIZE
									+ BCV_STACK_OVERFLOW_BUFFER_UDATA_SIZE) * sizeof(UDATA);
						
			ALLOC_BUFFER(verifyData->liveStack, verifyData->stackSize);

			x = 0;	
			if (0 == strncmp(J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)), "org/bouncycastle/jce/provider/BouncyCastleProvider", 50) && 0 == strncmp(J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)), "setParameter", 12)) x=1;
			length = (UDATA) (J9_BYTECODE_SIZE_FROM_ROM_METHOD(romMethod));
			mapLength = length * sizeof(U_32);
			if(x) printf("v00. romMethod=%p length=0x%x mapLength=0x%x\n", romMethod, length, mapLength);
			
			ALLOC_BUFFER(verifyData->bytecodeMap, mapLength);
			bytecodeMap = verifyData->bytecodeMap;
			
_fallBack:
			x = 0;	
			if (0 == strncmp(J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)), "org/bouncycastle/jce/provider/BouncyCastleProvider", 50) && 0 == strncmp(J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)), "setParameter", 12)) x=1;
			memset(bytecodeMap, 0, mapLength);
			createStackMaps = !classVersionRequiresStackmaps && (verifyData->ignoreStackMaps || !hasStackMaps);
			if(x) printf("v0. bytecodeMap=%p, mapLength=0x%x\n", bytecodeMap, mapLength);							
			if(x) printf("v1.classVersionRequiresStackmaps=%d verifyData->ignoreStackMaps=%d hasStackMaps=%d\n", classVersionRequiresStackmaps, verifyData->ignoreStackMaps, hasStackMaps);
			if (createStackMaps) {
				if(x) printf("v2.Before calling buildBranchMap verifyData=%p verifyData->bytecodeMap=%p printing verifyData->bytecodeMap ....\n", verifyData, verifyData->bytecodeMap);
				if(x) printBytes(verifyData->bytecodeMap, mapLength);
				verifyData->stackMapsCount = buildBranchMap(verifyData);
				if(x) printf("v3.After calling buildBranchMap verifyData=%p verifyData->stackMapsCount=%d verifyData->bytecodeMap=%p, printing verifyData->bytecodeMap ....\n", verifyData, verifyData->stackMapsCount, verifyData->bytecodeMap);
				if(x) printBytes(verifyData->bytecodeMap, mapLength);
				if (verifyData->stackMapsCount == (UDATA)BCV_ERR_INTERNAL_ERROR) {
					BUILD_VERIFY_ERROR(J9NLS_BCV_ERR_BYTECODES_INVALID__MODULE, J9NLS_BCV_ERR_BYTECODES_INVALID__ID);
					result = BCV_ERR_INTERNAL_ERROR;
					if(x) printf("v4.\tverifyData->stackMapsCount (%d) BCV_ERR_INTERNAL_ERROR=%d\n", verifyData->stackMapsCount, (UDATA)BCV_ERR_INTERNAL_ERROR);
					break;
				}
			} else {
				
				U_32 *stackMapMethod = getStackMapInfoForROMMethod(romMethod);

				verifyData->stackMapsCount = 0;
				stackMapData = 0;

				if(x) printf("v5.stackMapMethod=%p\n", stackMapMethod);
				/*Access the stored stack map data for this method, get pointer and map count */
				if (stackMapMethod) {
					stackMapData = (U_8 *)(stackMapMethod + 1);
					if(x) printf("v6.stackMapMethod (%p) is true. stackMapData=%p\n", stackMapMethod, stackMapData);
					if (x && stackMapData != NULL) printf("\tstackMapData=%s\n", stackMapData); 
					NEXT_U16(verifyData->stackMapsCount, stackMapData);
					if(x) printf("v7.after NEXT_U16 : stackMapMethod (%p) is true. stackMapData=%p\n", stackMapMethod, stackMapData);
					if (x && stackMapData != NULL) printf("\tstackMapData=%s\n", stackMapData);
				}
			}
		
			stackMapsSize = (verifyData->stackSize) * (verifyData->stackMapsCount);
			if(x) printf("v8.stackMapsSize=%d verifyData->stackSize=%d, verifyData->stackMapsCount=%d\n", stackMapsSize, verifyData->stackSize, verifyData->stackMapsCount);
			ALLOC_BUFFER(verifyData->stackMaps, stackMapsSize);
			if(x) printf("v8.5 after ALLOC_BUFFER printing verifyData->stackMaps  printing verifyData->stackMaps .................\n");
			if(x) printBytes(verifyData->stackMaps, stackMapsSize);
			if (createStackMaps && verifyData->stackMapsCount) {
				UDATA mapIndex = 0;
				/* Non-empty internal stackMap created */
				verifyData->createdStackMap = TRUE;
	
				liveStack = BCV_FIRST_STACK ();
				if(x) printf("v9.createStackMaps=%d verifyData->stackMapsCount=%d liveStack=%p\n", createStackMaps, verifyData->stackMapsCount, liveStack);
				/* Initialize stackMaps */
				for (j = 0; j < length; j++) {
					if(x) printf("v10.\tj=%d length=%d bytecodeMap[%d]=0x%x\n", j, length, j, (bytecodeMap)[j]);
					if ((bytecodeMap)[j] & BRANCH_TARGET) {
						if(x) printf("v10.2. bytecodeMap[%d](0x%x) & BRANCH_TARGET(0x%x) liveStack=%p\n", j, bytecodeMap[j], BRANCH_TARGET, liveStack);
						liveStack->pc = j;		/* offset of the branch target */
						liveStack->stackBaseIndex = -1;
						liveStack->stackTopIndex = -1;
						liveStack = BCV_NEXT_STACK (liveStack);
						(bytecodeMap)[j] |= (mapIndex << BRANCH_INDEX_SHIFT);
						if(x) printf("v10.4. bytecodeMap[%d]=0x%x, mapIndex=0x%x, BRANCH_INDEX_SHIFT=0x%x\n", j, bytecodeMap[j], mapIndex, BRANCH_INDEX_SHIFT);
						mapIndex++;
						if(x) printf("v10.6. mapIndex=0x%x\n", mapIndex);
					}
				}
	
				rootQueueSize = (verifyData->stackMapsCount + 1) * sizeof(UDATA);
				if(x) printf("v11.rootQueueSize=%d verifyData->stackMapsCount=%d sizeof(UDATA)=%d\n", rootQueueSize, verifyData->stackMapsCount, sizeof(UDATA));

				if (rootQueueSize > verifyData->rootQueueSize) {
					if(x) printf("v12.rootQueueSize(%d) > verifyData->rootQueueSize(%d)\n", rootQueueSize, verifyData->rootQueueSize);
					bcvfree(verifyData, verifyData->unwalkedQueue);
					verifyData->unwalkedQueue = bcvalloc(verifyData, rootQueueSize);
					if(x) printf("v13.rootQueueSize(%d) > verifyData->rootQueueSize(%d) verifyData->unwalkedQueue=%p\n", rootQueueSize, verifyData->rootQueueSize, verifyData->unwalkedQueue);
					bcvfree(verifyData, verifyData->rewalkQueue);
					verifyData->rewalkQueue = bcvalloc(verifyData, rootQueueSize);
					verifyData->rootQueueSize = rootQueueSize;
					if(x) printf("v14.rootQueueSize(%d) > verifyData->rootQueueSize(%d) verifyData->rewalkQueue=%p verifyData->rootQueueSize=%d\n", rootQueueSize, verifyData->rootQueueSize, verifyData->rewalkQueue,verifyData->rootQueueSize);
					if (!(verifyData->unwalkedQueue && verifyData->rewalkQueue)) {
						result = BCV_ERR_INSUFFICIENT_MEMORY;
						if(x) printf("v15.!(verifyData->unwalkedQueue && verifyData->rewalkQueue : result=BCV_ERR_INSUFFICIENT_MEMORY (%d)\n", BCV_ERR_INSUFFICIENT_MEMORY);
						break;
					}
				}
			}

			liveStack = (J9BranchTargetStack *) verifyData->liveStack;
			stackTop = &(liveStack->stackElements[0]);
	
			isInitMethod = buildStackFromMethodSignature(verifyData, &stackTop, &argCount);
	
			SAVE_STACKTOP(liveStack, stackTop);
			liveStack->stackBaseIndex = liveStack->stackTopIndex;
			if(x) printf("v16.liveStack=%p stackTop=%p, isInitMethod=%d liveStack->stackBaseIndex=%d verifyData->stackMapsCount=%d\n", liveStack, stackTop, isInitMethod, liveStack->stackBaseIndex, verifyData->stackMapsCount);
			result = 0;
			if (verifyData->stackMapsCount) {
				if (createStackMaps) {
					if(x) printf("v17.Before calling simulateStack verifyData=%p\n", verifyData);
					result = simulateStack (verifyData);
					if(x) printf("v18.After calling simulateStack verifyData=%p\n", verifyData);
				} else {
					if(x) printf("v19.Before calling decompressStackMaps verifyData=%p argCount=%d, stackMapData=%p\n", verifyData, argCount, stackMapData);
					if(x && stackMapData != NULL) printf("stackMapData=%s\n", stackMapData);
					result = decompressStackMaps (verifyData, argCount, stackMapData);
					if(x) printf("v20.After calling decompressStackMaps verifyData=%p argCount=%d, stackMapData=%p\n", verifyData, argCount, stackMapData);
					if(x && stackMapData != NULL) printf("v21.stackMapData=%s\n", stackMapData);
				}
			}
			
			if (BCV_ERR_INSUFFICIENT_MEMORY == result) {
				if(x) printf("v22. BCV_ERR_INSUFFICIENT_MEMORY == result(%d)\n", result);
				goto _done;
			}

			/* If stack maps created */
			/* Only perform second verification pass with a valid J9Class */
			if ((result == BCV_SUCCESS) && clazz) {
				if(x) printf("v23. (result (%d) == BCV_SUCCESS(%d)) && clazz(%p)\n", result,BCV_SUCCESS, clazz);
				if (isInitMethod) {
					if(x) printf("v24. isInitMethod (%d) verifyData=%p\n", isInitMethod, verifyData);
					/* CMVC 199785: Jazz103 45899: Only run this when the stack has been built correctly */
					setInitializedThisStatus(verifyData);
					if(x) printf("v25. isInitMethod (%d) verifyData=%p\n", isInitMethod, verifyData);
					
				}

				if (newFormat && verboseVerification) {
					if(x) printf("v26. newFormat(0x%x) && verboseVerification(0x%x)\n", newFormat, verboseVerification);
					ALWAYS_TRIGGER_J9HOOK_VM_METHOD_VERIFICATION_START(verifyData->javaVM->hookInterface, verifyData);
					if(x) printf("v27. newFormat(0x%x) && verboseVerification(0x%x)\n", newFormat, verboseVerification);
				}
				
				
				if(x) printf("v28. before calling j9rtv_verifyBytecodes() : verifyData=%p\n", verifyData);
				result = j9rtv_verifyBytecodes (verifyData);
				if(x) printf("v29. after calling j9rtv_verifyBytecodes() : verboseVerification=%p\n", verifyData);

				if (BCV_ERR_INSUFFICIENT_MEMORY == result) {
					if(x) printf("v30. BCV_ERR_INSUFFICIENT_MEMORY(0x%x) == result(0x%x)\n", BCV_ERR_INSUFFICIENT_MEMORY, result);
					goto _done;
				}

				if (newFormat && verboseVerification) {
					BOOLEAN willFailOver = FALSE;
					if(x) printf("v31. newFormat(0x%x) == verboseVerification(0x%x)\n", newFormat, verboseVerification);
					/*
					 * If verification failed and will fail over to older verifier, we only output stack map frame details
					 * if the frame count is bigger than 0.
					 */
					if ((BCV_SUCCESS != result)
						&& !classVersionRequiresStackmaps
						&& !createStackMaps
						&& (J9_VERIFY_NO_FALLBACK != (verifyData->verificationFlags & J9_VERIFY_NO_FALLBACK))) {
						if(x) printf("v32. willFailOver = TRUE\n");
						willFailOver = TRUE;
					}

					if (!willFailOver || (verifyData->stackMapsCount > 0)) {
						if(x) printf("v33. !willFailOver(%d) || (verifyData->stackMapsCount (%d) > 0)\n", willFailOver, verifyData->stackMapsCount);
						ALWAYS_TRIGGER_J9HOOK_VM_STACKMAPFRAME_VERIFICATION(verifyData->javaVM->hookInterface, verifyData);
						if(x) printf("v34. after calling ALWAYS_TRIGGER_J9HOOK_VM_STACKMAPFRAME_VERIFICATION()\n");
					}
				}
			}
			/* If verify error */
			if (result) {
				if(x) printf("v35. result=%d\n", result);
				/* Check verification fallback criteria */
				if (classVersionRequiresStackmaps || createStackMaps || (verifyData->verificationFlags & J9_VERIFY_NO_FALLBACK)) {
					/* no retry */
					result = BCV_ERR_INTERNAL_ERROR;
					if(x) printf("v36. classVersionRequiresStackmaps(0x%x) || createStackMaps(0x%x) || (verifyData->verificationFlags(0x%x) & J9_VERIFY_NO_FALLBACK(0x%x))\n", classVersionRequiresStackmaps, createStackMaps, verifyData->verificationFlags, J9_VERIFY_NO_FALLBACK);
					break;
				} else {
					if(x) printf("v37. before calling RESET_VERIFY_ERROR(verifyData(%p))\n", verifyData);
					/* reset verification failure */
					RESET_VERIFY_ERROR(verifyData);
					verifyData->errorPC = (UDATA) 0;
					verifyData->errorModule = 0;
					verifyData->errorCode = 0;				
					
					Trc_BCV_j9bcv_verifyBytecodes_ReverifyMethod(verifyData->vmStruct,
							(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(romClass)),
							J9UTF8_DATA(J9ROMCLASS_CLASSNAME(romClass)),
							(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
							J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
							(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
							J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)));

					/* retry with ignoreStackMaps enabled */
					verifyData->ignoreStackMaps = TRUE;

					if (verboseVerification) {
						newFormat = FALSE;
						if(x) printf("v37.5. before ALWAYS_TRIGGER_J9HOOK_VM_CLASS_VERIFICATION_FALLBACK verifyData=%p newFormat=%d\n", verifyData, newFormat);
						ALWAYS_TRIGGER_J9HOOK_VM_CLASS_VERIFICATION_FALLBACK(verifyData->javaVM->hookInterface, verifyData, newFormat);
					}
					if(x) printf("v38. before _fallBack\n");
					goto _fallBack;
				}
			}
		}
		if(x) printf("v39. before romMethod = J9_NEXT_ROM_METHOD(romMethod)\n");
		romMethod = J9_NEXT_ROM_METHOD(romMethod);
		if(x) printf("v40. after romMethod = J9_NEXT_ROM_METHOD(romMethod) verifyData=%p\n", verifyData);		
	}
	if(x) printf("v40.5.\n");
_done:
	if(x) printf("v41. done\n");
	verifyData->vmStruct->omrVMThread->vmState = oldState;
	if(x) printf("v41. done\n");
	if (result == BCV_ERR_INSUFFICIENT_MEMORY) {
		Trc_BCV_j9bcv_verifyBytecodes_OutOfMemory(verifyData->vmStruct, 
				(UDATA) J9UTF8_LENGTH(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				J9UTF8_DATA(J9ROMCLASS_CLASSNAME(verifyData->romClass)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_NAME(romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_NAME(romMethod)),
				(UDATA) J9UTF8_LENGTH(J9ROMMETHOD_SIGNATURE(romMethod)),
				J9UTF8_DATA(J9ROMMETHOD_SIGNATURE(romMethod)));
		if(x) printf("v42. result(%d) == BCV_ERR_INSUFFICIENT_MEMORY(%d)\n", result, BCV_ERR_INSUFFICIENT_MEMORY);
	}

	if (verboseVerification) {
		if(x) printf("v43. verboseVerification=%d verifyData=%p, newFormat=%d\n", verboseVerification, verifyData, newFormat);
		ALWAYS_TRIGGER_J9HOOK_VM_CLASS_VERIFICATION_END(verifyData->javaVM->hookInterface, verifyData, newFormat);
		if(x) printf("v44. after calling ALWAYS_TRIGGER_J9HOOK_VM_CLASS_VERIFICATION_END()\n", verboseVerification);
	}

	Trc_BCV_j9bcv_verifyBytecodes_Exit(verifyData->vmStruct, result);
	if(x) printf("v45. returnning result=%d\n", result);
	return result;
}
#undef ALLOC_BUFFER


/*
 * returns J9VMDLLMAIN_OK on success
 * returns J9VMDLLMAIN_FAILED on error
 */
IDATA  
j9bcv_J9VMDllMain (J9JavaVM* vm, IDATA stage, void* reserved)
{
	J9BytecodeVerificationData* verifyData = NULL;
	char optionValuesBuffer[128];					/* Needs to be big enough to hold -Xverify option values */
	char* optionValuesBufferPtr = optionValuesBuffer;
	J9VMDllLoadInfo* loadInfo = NULL;
	IDATA xVerifyIndex = -1;
	IDATA xVerifyColonIndex = -1;
	IDATA verboseVerificationIndex = -1;
	IDATA noVerboseVerificationIndex = -1;
	IDATA verifyErrorDetailsIndex = -1;
	IDATA noVerifyErrorDetailsIndex = -1;
	IDATA classRelationshipVerifierIndex = -1;
	IDATA noClassRelationshipVerifierIndex = -1;
	IDATA returnVal = J9VMDLLMAIN_OK;
#if defined(J9VM_GC_DYNAMIC_CLASS_UNLOADING)
	J9HookInterface ** vmHooks = vm->internalVMFunctions->getVMHookInterface(vm);
#endif /* J9VM_GC_DYNAMIC_CLASS_UNLOADING */

	PORT_ACCESS_FROM_JAVAVM(vm);

	switch(stage) {

		case ALL_VM_ARGS_CONSUMED :
			FIND_AND_CONSUME_ARG( OPTIONAL_LIST_MATCH, OPT_XVERIFY, NULL);
			break;

		case BYTECODE_TABLE_SET :
			loadInfo = FIND_DLL_TABLE_ENTRY( THIS_DLL_NAME );
			verifyData = j9bcv_initializeVerificationData(vm);
			if( !verifyData ) {
				loadInfo->fatalErrorStr = "j9bcv_initializeVerificationData failed";
				returnVal = J9VMDLLMAIN_FAILED;
				break;
			}

			vm->bytecodeVerificationData = verifyData;
			vm->runtimeFlags |= J9_RUNTIME_VERIFY;

#if defined(J9VM_GC_DYNAMIC_CLASS_UNLOADING) 
			if ((*vmHooks)->J9HookRegisterWithCallSite(vmHooks, J9HOOK_VM_CLASSES_UNLOAD, bcvHookClassesUnload, OMR_GET_CALLSITE(), vm)) {
				returnVal = J9VMDLLMAIN_FAILED;
				break;
			}
#endif /* J9VM_GC_DYNAMIC_CLASS_UNLOADING */

			/* Parse the -Xverify and -Xverify:<opt> commandline options.
			 * Rules:
			 * 1. -Xverify skips any previous -Xverify:<opt> arguments.  -Xverify is the default state.
			 * 2. Any -Xverify:<opt> prior to -Xverify is ignored.
			 * 3. All -Xverify:<opt> after the -Xverify are processed in left-to-right order.
			 * 4. -Xverify:<opt>,<opt> etc is also valid.
			 * 5. -Xverify: is an error.
			 * 6. -Xverify:<opt> processing occurs in the parseOptions function.
			 *
			 * This parsing is a duplicate of the parsing in the function VMInitStages of jvminit.c
			 */
			xVerifyIndex = FIND_ARG_IN_VMARGS( EXACT_MATCH, OPT_XVERIFY, NULL);
			xVerifyColonIndex = FIND_ARG_IN_VMARGS_FORWARD( STARTSWITH_MATCH, OPT_XVERIFY_COLON, NULL);
			while (xVerifyColonIndex >= 0) {
				/* Ignore -Xverify:<opt>'s prior to the the last -Xverify */
				if (xVerifyColonIndex > xVerifyIndex) {
					/* Deal with possible -Xverify:<opt>,<opt> case */
					GET_OPTION_VALUES( xVerifyColonIndex, ':', ',', &optionValuesBufferPtr, 128 );

					if(*optionValuesBuffer) {
						if (!parseOptions(vm, optionValuesBuffer, &loadInfo->fatalErrorStr)) {
							returnVal = J9VMDLLMAIN_FAILED;
						}
					} else {
						loadInfo->fatalErrorStr = "No options specified for -Xverify:<opt>";
						returnVal = J9VMDLLMAIN_FAILED;
					}
				}
				/* Advance to next argument */
				xVerifyColonIndex = FIND_NEXT_ARG_IN_VMARGS_FORWARD(STARTSWITH_MATCH, OPT_XVERIFY_COLON, NULL, xVerifyColonIndex);
			}

			verboseVerificationIndex = FIND_AND_CONSUME_ARG(EXACT_MATCH, VMOPT_XXVERBOSEVERIFICATION, NULL);
			noVerboseVerificationIndex = FIND_AND_CONSUME_ARG(EXACT_MATCH, VMOPT_XXNOVERBOSEVERIFICATION, NULL);
			if (verboseVerificationIndex > noVerboseVerificationIndex) {
				vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_VERBOSE_VERIFICATION;
			}

			verifyErrorDetailsIndex = FIND_AND_CONSUME_ARG(EXACT_MATCH, VMOPT_XXVERIFYERRORDETAILS, NULL);
			noVerifyErrorDetailsIndex = FIND_AND_CONSUME_ARG(EXACT_MATCH, VMOPT_XXNOVERIFYERRORDETAILS, NULL);
			if (verifyErrorDetailsIndex >= noVerifyErrorDetailsIndex) {
				vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_ERROR_DETAILS;
			}

			/* Set runtime flag for -XX:+ClassRelationshipVerifier */
			classRelationshipVerifierIndex = FIND_AND_CONSUME_ARG(EXACT_MATCH, VMOPT_XXCLASSRELATIONSHIPVERIFIER, NULL);
			noClassRelationshipVerifierIndex = FIND_AND_CONSUME_ARG(EXACT_MATCH, VMOPT_XXNOCLASSRELATIONSHIPVERIFIER, NULL);
			if (classRelationshipVerifierIndex > noClassRelationshipVerifierIndex) {
				if (J9_ARE_ANY_BITS_SET(vm->runtimeFlags, J9_RUNTIME_XFUTURE)) {
					loadInfo->fatalErrorStr = "-XX:+ClassRelationshipVerifier cannot be used if -Xfuture or if -Xverify:all is enabled";
					returnVal = J9VMDLLMAIN_FAILED;
				} else {
					vm->extendedRuntimeFlags2 |= J9_EXTENDED_RUNTIME2_ENABLE_CLASS_RELATIONSHIP_VERIFIER;
				}
			}

			break;

		case LIBRARIES_ONUNLOAD :
			if (vm->bytecodeVerificationData) {
				j9bcv_freeVerificationData(PORTLIB, vm->bytecodeVerificationData);
#if defined(J9VM_GC_DYNAMIC_CLASS_UNLOADING) 
				(*vmHooks)->J9HookUnregister(vmHooks, J9HOOK_VM_CLASSES_UNLOAD, bcvHookClassesUnload, vm);
#endif /* J9VM_GC_DYNAMIC_CLASS_UNLOADING */
			}
			break;
	}
	return returnVal;
}


static IDATA 
setVerifyState(J9JavaVM *vm, char *option, char **errorString)
{
	PORT_ACCESS_FROM_JAVAVM(vm);

	if (0 == strcmp(option, OPT_ALL)) {
		/* JDK7 - CMVC 151154: Sun launcher converts -Xfuture to -Xverify:all */
		vm->runtimeFlags |= J9_RUNTIME_XFUTURE;
		vm->bytecodeVerificationData->verificationFlags &= ~J9_VERIFY_SKIP_BOOTSTRAP_CLASSES;
	} else if (0 == strcmp(option, OPT_OPT)) {
		/* on by default - will override a "noopt" before it */
		vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_OPTIMIZE;
	} else if (0 == strcmp(option, OPT_NO_OPT)) {
		vm->bytecodeVerificationData->verificationFlags &= ~J9_VERIFY_OPTIMIZE;
	} else if (0 == strcmp(option, OPT_NO_FALLBACK)) {
		vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_NO_FALLBACK;
	} else if (0 == strcmp(option, OPT_IGNORE_STACK_MAPS)) {
		vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_IGNORE_STACK_MAPS;
	} else if (0 == strncmp(option, OPT_EXCLUDEATTRIBUTE_EQUAL, sizeof(OPT_EXCLUDEATTRIBUTE_EQUAL) - 1)) {
		if (0 != option[sizeof(OPT_EXCLUDEATTRIBUTE_EQUAL)]) {
			UDATA length;
			vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_EXCLUDE_ATTRIBUTE;
			/* Save the parameter string, NULL terminated and the length excluding the NULL */
			length = strlen(option) - sizeof(OPT_EXCLUDEATTRIBUTE_EQUAL) + 1;
			vm->bytecodeVerificationData->excludeAttribute = j9mem_allocate_memory(length + 1, J9MEM_CATEGORY_CLASSES);
			if (NULL == vm->bytecodeVerificationData->excludeAttribute) {
				if (errorString) {
					*errorString = "Out of memory processing -Xverify:<opt>";
				}
				return FALSE;
			}
			memcpy(vm->bytecodeVerificationData->excludeAttribute, &(option[sizeof(OPT_EXCLUDEATTRIBUTE_EQUAL) - 1]), length + 1);
		}
	} else if (0 == strcmp(option, OPT_BOOTCLASSPATH_STATIC)) {
		vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_BOOTCLASSPATH_STATIC;
	} else if (0 == strcmp(option, OPT_DO_PROTECTED_ACCESS_CHECK)) {
		vm->bytecodeVerificationData->verificationFlags |= J9_VERIFY_DO_PROTECTED_ACCESS_CHECK;
	} else {
		if (errorString) {
			*errorString = "Unrecognised option(s) for -Xverify:<opt>";
		}
		return FALSE;
	}
	return TRUE;
}



static IDATA 
parseOptions(J9JavaVM *vm, char *optionValues, char **errorString) 
{
	char *optionValue = optionValues;			/* Values are separated by single NULL characters. */

	/* call setVerifyState on each individual option */
	while (*optionValue) {
		if( !setVerifyState( vm, optionValue, errorString ) ) {
			return FALSE;
		}
		optionValue = optionValue + strlen(optionValue) + 1;			/* Step past null separator to next element */
	}
	return TRUE;
}


#if defined(J9VM_GC_DYNAMIC_CLASS_UNLOADING) 
/**
 * Unlink any constraints related to dying classloaders
 */
static void 
bcvHookClassesUnload(J9HookInterface** hook, UDATA eventNum, void* eventData, void* userData)
{
	J9JavaVM *javaVM = userData;

	if (0 != (javaVM->runtimeFlags & J9_RUNTIME_VERIFY)) {
		unlinkClassLoadingConstraints(javaVM);
	}
}
#endif /* J9VM_GC_DYNAMIC_CLASS_UNLOADING */


