package de.hentschel.visualdbc.key.ui.test.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import de.hentschel.visualdbc.key.ui.test.testCase.ProofReferenceModelCreatorTest;

/**
 * Run all contained JUnit 4 test cases.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   ProofReferenceModelCreatorTest.class
})
public class AllKeYUiTests {
}
