package org.key_project.sed.core.all.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.key_project.key4eclipse.starter.core.test.suite.AllStarterCoreTests;
import org.key_project.key4eclipse.test.suite.AllKeY4EclipseTests;
import org.key_project.sed.key.core.test.suite.AllSEDKeYTests;
import org.key_project.sed.key.ui.test.suite.AllSEDKeYUITests;
import org.key_project.util.test.suite.AllUtilTests;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
    AllKeY4EclipseTests.class,
    AllUtilTests.class,
    AllStarterCoreTests.class,
    AllSEDKeYTests.class,
    AllSEDKeYUITests.class
})
public class AllSEDTests {
}
