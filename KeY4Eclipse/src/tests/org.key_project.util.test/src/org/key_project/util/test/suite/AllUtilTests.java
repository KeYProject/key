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

package org.key_project.util.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.util.suite.AllUtilsTests;
import org.key_project.util.test.testcase.AbstractBeanViewPartTest;
import org.key_project.util.test.testcase.AbstractRunnableWithProgressAndResultTest;
import org.key_project.util.test.testcase.AbstractRunnableWithResultTest;
import org.key_project.util.test.testcase.AbstractViewBasedViewTest;
import org.key_project.util.test.testcase.BeanCompositeTest;
import org.key_project.util.test.testcase.BeanTest;
import org.key_project.util.test.testcase.BundleUtilTest;
import org.key_project.util.test.testcase.ButtonViewerTest;
import org.key_project.util.test.testcase.JDTUtilTest;
import org.key_project.util.test.testcase.JobUtilTest;
import org.key_project.util.test.testcase.LoggerTest;
import org.key_project.util.test.testcase.ResourceUtilTest;
import org.key_project.util.test.testcase.SWTUtilTest;
import org.key_project.util.test.testcase.ScheduledJobCollectorTest;
import org.key_project.util.test.testcase.WorkbenchUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    AllUtilsTests.class,
    AbstractBeanViewPartTest.class,
    AbstractRunnableWithResultTest.class,
    AbstractRunnableWithProgressAndResultTest.class,
    AbstractRunnableWithResultTest.class,
    AbstractViewBasedViewTest.class,
    BeanCompositeTest.class,
    BeanTest.class,
    BundleUtilTest.class,
    ButtonViewerTest.class,
    JDTUtilTest.class,
    JobUtilTest.class,
    LoggerTest.class,
    ResourceUtilTest.class,
    ScheduledJobCollectorTest.class,
    SWTUtilTest.class,
    WorkbenchUtilTest.class
})
public class AllUtilTests {
}