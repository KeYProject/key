package org.key_project.key4eclipse.starter.core.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.starter.core.test.testcase.ImmutableCollectionContentProviderTest;
import org.key_project.key4eclipse.starter.core.test.testcase.JavaElementResourceAdapterFactoryTest;
import org.key_project.key4eclipse.starter.core.test.testcase.JavaTextSelectionPropertyTesterTest;
import org.key_project.key4eclipse.starter.core.test.testcase.KeYUtilTest;
import org.key_project.key4eclipse.starter.core.test.testcase.LogUtilTest;
import org.key_project.key4eclipse.starter.core.test.testcase.NodePreorderIteratorTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    ImmutableCollectionContentProviderTest.class,
    JavaElementResourceAdapterFactoryTest.class,
    JavaTextSelectionPropertyTesterTest.class,
    KeYUtilTest.class,
    LogUtilTest.class,
    NodePreorderIteratorTest.class
})
public class AllStarterCoreTests {
}
