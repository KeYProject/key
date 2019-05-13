package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        de.uka.ilkd.key.util.TestLexicographicComparator.class,
        de.uka.ilkd.key.util.TestVersionStringComparator.class,
        de.uka.ilkd.key.util.TestMiscTools.class,
        de.uka.ilkd.key.util.pp.TestLayouter.class,
        de.uka.ilkd.key.util.TestProofStarter.class,
        de.uka.ilkd.key.util.TestNodePreorderIterator.class,
        de.uka.ilkd.key.util.TestSearchNodePreorderIterator.class,
        de.uka.ilkd.key.util.TestSearchNodeReversePreorderIterator.class,
        de.uka.ilkd.key.util.TestProofUserManager.class,
        de.uka.ilkd.key.rule.merge.PredicateAbstractionLatticeTests.class,
        de.uka.ilkd.key.proof.io.TestZipProofSaving.class
})
public class UtilityTests {
}