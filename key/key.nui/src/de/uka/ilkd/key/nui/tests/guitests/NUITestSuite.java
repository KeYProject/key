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
@Suite.SuiteClasses({ AddNewFilterTest.class, AddNewViewTest.class,
        FilterViewTest.class, LoadProofTest.class, MoveViewTest.class,
        NUITest.class, SearchViewTest.class, StandardFilterTest.class,
        StrategyViewTest.class, TreeViewTest.class })

@SuppressWarnings("PMD.AtLeastOneConstructor")
// PMD will also complain if adding the constructor, then saying "avoid useless
// constructors"
public class NUITestSuite {
}