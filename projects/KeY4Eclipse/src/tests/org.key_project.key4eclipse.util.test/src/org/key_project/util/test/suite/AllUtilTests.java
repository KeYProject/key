package org.key_project.util.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.util.test.testcase.AbstractRunnableWithProgressAndResultTest;
import org.key_project.util.test.testcase.AbstractRunnableWithResultTest;
import org.key_project.util.test.testcase.ArrayUtilTest;
import org.key_project.util.test.testcase.BeanTest;
import org.key_project.util.test.testcase.BundleUtilTest;
import org.key_project.util.test.testcase.CollectionUtilTest;
import org.key_project.util.test.testcase.DefaultEntryTest;
import org.key_project.util.test.testcase.IOUtilTest;
import org.key_project.util.test.testcase.JDTUtilTest;
import org.key_project.util.test.testcase.LoggerTest;
import org.key_project.util.test.testcase.ObjectUtilTest;
import org.key_project.util.test.testcase.ResourceUtilTest;
import org.key_project.util.test.testcase.SWTUtilTest;
import org.key_project.util.test.testcase.StringUtilTest;
import org.key_project.util.test.testcase.WorkbenchUtilTest;
import org.key_project.util.test.testcase.XMLUtilTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    AbstractRunnableWithResultTest.class,
    AbstractRunnableWithProgressAndResultTest.class,
    AbstractRunnableWithResultTest.class,
    ArrayUtilTest.class,
    BeanTest.class,
    BundleUtilTest.class,
    CollectionUtilTest.class,
    DefaultEntryTest.class,
    IOUtilTest.class,
    JDTUtilTest.class,
    LoggerTest.class,
    ObjectUtilTest.class,
    ResourceUtilTest.class,
    StringUtilTest.class,
    SWTUtilTest.class,
    WorkbenchUtilTest.class,
    XMLUtilTest.class
})
public class AllUtilTests {
}
