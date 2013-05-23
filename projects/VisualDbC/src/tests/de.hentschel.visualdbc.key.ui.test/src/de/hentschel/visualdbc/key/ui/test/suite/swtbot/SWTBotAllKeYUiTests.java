package de.hentschel.visualdbc.key.ui.test.suite.swtbot;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

import de.hentschel.visualdbc.key.ui.test.testCase.swtbot.SWTBotProofProviderAdapterFactoryTest;

/**
 * Run all contained JUnit 4 test cases that requires SWT Bot.
 * @author Martin Hentschel
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({
   SWTBotProofProviderAdapterFactoryTest.class
})
public class SWTBotAllKeYUiTests {

}
