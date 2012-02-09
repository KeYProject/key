package org.key_project.key4eclipse.util.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.util.test.testcase.AbstractRunnableWithProgressAndResultTest;
import org.key_project.key4eclipse.util.test.testcase.AbstractRunnableWithResultTest;
import org.key_project.key4eclipse.util.test.testcase.ArrayUtilTest;
import org.key_project.key4eclipse.util.test.testcase.BeanTest;
import org.key_project.key4eclipse.util.test.testcase.BundleUtilTest;
import org.key_project.key4eclipse.util.test.testcase.CollectionUtilTest;
import org.key_project.key4eclipse.util.test.testcase.IOUtilTest;
import org.key_project.key4eclipse.util.test.testcase.JDTUtilTest;
import org.key_project.key4eclipse.util.test.testcase.LoggerTest;
import org.key_project.key4eclipse.util.test.testcase.ObjectUtilTest;
import org.key_project.key4eclipse.util.test.testcase.ResourceUtilTest;
import org.key_project.key4eclipse.util.test.testcase.SWTUtilTest;
import org.key_project.key4eclipse.util.test.testcase.StringUtilTest;
import org.key_project.key4eclipse.util.test.testcase.WorkbenchUtilTest;

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
    IOUtilTest.class,
    JDTUtilTest.class,
    LoggerTest.class,
    ObjectUtilTest.class,
    ResourceUtilTest.class,
    StringUtilTest.class,
    SWTUtilTest.class,
    WorkbenchUtilTest.class
})
public class AllUtilTests {
}
