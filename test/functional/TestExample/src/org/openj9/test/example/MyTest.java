/*******************************************************************************
 * Copyright (c) 2001, 2018 IBM Corp. and others
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
package org.openj9.test.example;

import org.testng.AssertJUnit;
import org.testng.annotations.Test;
import org.testng.log4testng.Logger;

import j9vm.test.ddrext.util.parser.ClassForNameOutputParser;
import j9vm.test.ddrext.DDRExtTesterBase;
//import com.ibm.j9ddr.vm29.pointer.helper.J9JavaVMHelper;
//import com.ibm.j9ddr.vm29.view.dtfj.DTFJContext;
import java.util.Properties;
import j9vm.test.ddrext.Constants;

/*
@Test(groups={ "level.extended" })
public class MyTest {

	private static Logger logger = Logger.getLogger(MyTest.class);
	
	public void aTestExample() {
		logger.info("running aTestExample: INFO and above level logging enabled");
		AssertJUnit.assertEquals(4, 2+2);
	}
}
*/
public class MyTest {
    public static void main(String[] args) {
		private static final String JAVA_LANG_SYSTEM = "java/lang/System";
		private static final String SYSTEMPROPERTIES = "systemProperties";

		String classForName = exec(Constants.CL_FOR_NAME_CMD, JAVA_LANG_SYSTEM);
		// may need to use the other classforname parser if there is more than one class that it outputted for this command
		String classForNameAddress = ClassForNameOutputParser.extractClassAddress(classForName);
		String j9Statics = exec(Constants.J9STATICS_CMD, new String[] { classForNameAddress });
		String j9StaticsAddress = ParserUtil.getFieldAddressOrValue(SYSTEMPROPERTIES, Constants.J9OBJECT_CMD ,j9Statics);
		String systemPropertiesObject = exec(Constants.J9OBJECT_CMD, j9StaticsAddress);

		/*
		Properties properties = new Properties();
		properties = J9JavaVMHelper.getSystemProperties(DTFJContext.getVm());
		String vmname = (String) properties.get("java.vm.name");
		*/
		//String vmname = (String) systemPropertiesObject.get("java.vm.name");
		//System.out.println("This is the vmname" + vmname);
    }
}
