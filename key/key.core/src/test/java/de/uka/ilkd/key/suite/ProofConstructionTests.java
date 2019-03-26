package de.uka.ilkd.key.suite;

import org.junit.runner.RunWith;
import org.junit.runners.Suite;

@RunWith(Suite.class)
@Suite.SuiteClasses({
        de.uka.ilkd.key.proof.TestTacletIndex.class,
        de.uka.ilkd.key.proof.TestProofTree.class,
        de.uka.ilkd.key.proof.TestGoal.class,
        de.uka.ilkd.key.proof.TestTermTacletAppIndex.class,
        de.uka.ilkd.key.taclettranslation.TestTacletTranslator.class,
        de.uka.ilkd.key.taclettranslation.lemma.TestGenericRemovingLemmaGenerator.class
})
public class ProofConstructionTests {
}