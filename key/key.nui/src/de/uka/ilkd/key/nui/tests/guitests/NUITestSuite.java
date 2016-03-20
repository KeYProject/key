package de.uka.ilkd.key.nui.tests.guitests;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

/**
 * Test Suite for all TestFX GUI tests.
 * 
 * @author Florian Breitfelder
 *
 */
@RunWith(Suite.class)
@Suite.SuiteClasses({ MoveViewTest.class, TreeViewTest.class, LoadProofTest.class,
        SearchViewTest.class })

public class NUITestSuite {
}