/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    org.key_project.util.testcase.java.ArrayUtilTest.class,
    org.key_project.util.testcase.java.CollectionUtilTest.class,
    org.key_project.util.testcase.java.IOUtilTest.class,
    org.key_project.util.testcase.java.NumberUtilTest.class,
    org.key_project.util.testcase.java.ObjectUtilTest.class,
    org.key_project.util.testcase.java.StringUtilTest.class,
    org.key_project.util.testcase.java.XMLUtilTest.class
})
public class AllJavaTests {
}