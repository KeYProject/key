package org.key_project.key4eclipse.common.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.common.ui.test.testcase.ImmutableCollectionContentProviderTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    ImmutableCollectionContentProviderTest.class
})
public class AllCommonUiTests {
}
