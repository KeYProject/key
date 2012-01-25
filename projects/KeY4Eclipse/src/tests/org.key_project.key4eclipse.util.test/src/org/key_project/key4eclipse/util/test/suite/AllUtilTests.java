/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.util.test.testcase.AbstractRunnableWithResultTest;
import org.key_project.key4eclipse.util.test.testcase.ArrayUtilTest;
import org.key_project.key4eclipse.util.test.testcase.BundleUtilTest;
import org.key_project.key4eclipse.util.test.testcase.CollectionUtilTest;
import org.key_project.key4eclipse.util.test.testcase.IOUtilTest;
import org.key_project.key4eclipse.util.test.testcase.JDTUtilTest;
import org.key_project.key4eclipse.util.test.testcase.LoggerTest;
import org.key_project.key4eclipse.util.test.testcase.ObjectUtilTest;
import org.key_project.key4eclipse.util.test.testcase.ResourceUtilTest;
import org.key_project.key4eclipse.util.test.testcase.StringUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    AbstractRunnableWithResultTest.class,
    AbstractRunnableWithResultTest.class,
    ArrayUtilTest.class,
    BundleUtilTest.class,
    CollectionUtilTest.class,
    IOUtilTest.class,
    JDTUtilTest.class,
    LoggerTest.class,
    ObjectUtilTest.class,
    ResourceUtilTest.class,
    StringUtilTest.class
})
public class AllUtilTests {
}
