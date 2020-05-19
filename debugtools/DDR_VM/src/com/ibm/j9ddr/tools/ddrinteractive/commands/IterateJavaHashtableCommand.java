/*******************************************************************************
 * Copyright (c) 2001, 2020 IBM Corp. and others
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
package com.ibm.j9ddr.tools.ddrinteractive.commands;

import java.io.PrintStream;

import com.ibm.j9ddr.tools.ddrinteractive.Context;
import com.ibm.j9ddr.tools.ddrinteractive.Command;
import com.ibm.j9ddr.tools.ddrinteractive.DDRInteractiveCommandException;
import com.ibm.j9ddr.tools.ddrinteractive.CommandUtils;
import com.ibm.j9ddr.vm29.pointer.generated.J9HashTablePointer;
import com.ibm.j9ddr.vm29.pointer.generated.J9BuildFlags;
import com.ibm.j9ddr.CorruptDataException;

public class IterateJavaHashtableCommand extends Command{
    //TODO: change to find key-value, as we are not iterating
    public IterateJavaHashtableCommand()
	{
		addCommand("findKeyValue", "<hashtable>", "search for key-value pair in a hashtable");
    }
    
    public void run(String command, String[] args, Context context, PrintStream out) throws DDRInteractiveCommandException {
        //check to make sure we are looking in a hashtable
        long address = CommandUtils.parsePointer(args[0], J9BuildFlags.env_data64);
        String key = args[1]; //check if this null
        try {
            if (args.length != 2) {
				CommandUtils.dbgPrint(out, "Usage: !findKeyValue <hashtable> <key>\n");
				return;
            }
            
            J9HashTablePointer table = J9HashTablePointer.cast(address);
            String value = table.get(key);

            if (null != value){
                CommandUtils.dbgPrint(out, "Value for key %s: %s\n", key, value);
            } else {
                CommandUtils.dbgPrint(out, "Key does not exist");
            }
        } catch (CorruptDataException e) {
			throw new DDRInteractiveCommandException(e);
        }
        
         
    }
}