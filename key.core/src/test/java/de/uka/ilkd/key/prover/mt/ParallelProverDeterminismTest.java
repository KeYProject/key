/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Path;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression test that the sequential prover and the 1-worker parallel prover construct the
 * <em>identical</em> proof. With a single worker there are no races, so any difference between the
 * two provers is a pure function of the goal hand-out order — which must not influence the proof,
 * because every cost input is supposed to be local to a goal's branch. Differences here have
 * historically been caused by shared caches leaking cross-goal state into rule selection (e.g. the
 * polarity-blind {@link de.uka.ilkd.key.proof.TermTacletAppIndexCacheSet} entries that made
 * candidate reporting depend on which goal indexed a term first), which under multiple workers
 * turns into run-to-run nondeterminism of the proof shape.
 */
public class ParallelProverDeterminismTest {

    /**
     * Small examples for which sequential and 1-worker proofs are identical, node for node.
     * (Of the variance-benchmark set only SimplifiedLinkedList.remove still differs — the other,
     * larger examples agree on the node count but are too expensive for a unit test, so this list
     * guards the fast examples the provers fully agree on against regressions.)
     */
    private static final String[] PROOFS = {
        "heap/block_contracts/Simple__add.key",
        "heap/block_contracts/Simple__addAbsoluteValues.key",
        "heap/block_contracts/Simple__addWithJump.key",
        "heap/block_contracts/Simple__addWithTwoBlockContracts.key",
        "heap/block_contracts/Simple__getLength.key",
        "heap/block_contracts/Simple__square.key",
        "heap/block_contracts/Simple__unnecessaryBlockContract.key",
        "heap/block_contracts/Simple__unnecessaryLoopInvariant.key",
    };

    private static final int MAX_STEPS = 20000;

    private static String settingsBaseline;
    private static String oldParallel;
    private static String oldThreads;

    @BeforeAll
    static void rememberEnvironment() {
        settingsBaseline = ProofSettings.DEFAULT_SETTINGS.settingsToString();
        oldParallel = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        oldThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
    }

    @AfterAll
    static void restoreEnvironment() {
        restoreProperty(ParallelProver.PARALLEL_PROPERTY, oldParallel);
        restoreProperty(ParallelProver.THREADS_PROPERTY, oldThreads);
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsBaseline);
    }

    private static void restoreProperty(String key, String value) {
        if (value == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, value);
        }
    }

    @Test
    void sequentialAndOneWorkerProofsAreIdentical() throws Exception {
        final Path examples = FindResources.getExampleDirectory();
        assertNotNull(examples, "examples directory not found");

        for (final String rel : PROOFS) {
            final Path file = examples.resolve(rel);
            final KeYEnvironment<?> seqEnv = prove(file, 0);
            final KeYEnvironment<?> w1Env = prove(file, 1);
            try {
                final Proof seq = seqEnv.getLoadedProof();
                final Proof w1 = w1Env.getLoadedProof();
                assertTrue(seq.closed(), rel + ": sequential proof did not close");
                assertTrue(w1.closed(), rel + ": 1-worker proof did not close");
                assertEquals(seq.countNodes(), w1.countNodes(),
                    rel + ": proof sizes differ between sequential and 1-worker prover");
                assertTreesEqual(rel, seq.root(), w1.root(), "");
            } finally {
                seqEnv.dispose();
                w1Env.dispose();
            }
        }
    }

    /**
     * Term-level identity (names included) is additionally asserted when
     * {@code -Dkey.naming.termlevel=true}: the #3851 end state. Currently still gated on ONE
     * remaining channel: block/loop-contract remembrance variables
     * ({@code AuxiliaryContract.Variables.createVariable}) draw their {@code #<n>} suffix from
     * the proof-global {@code VarNamerCnt} counter, which ticks differently between the
     * sequential and the parallel path (observed: {@code z_Before_BLOCK#25} vs {@code #28}).
     * Once that channel is branch-state-derived, the gate is removed.
     */
    private static final boolean TERM_LEVEL = Boolean.getBoolean("key.naming.termlevel");

    /**
     * Assert both proof trees applied the same rule at the same position at every tree path (and,
     * see {@link #TERM_LEVEL}, term-identical sequents including all fresh names).
     */
    private static void assertTreesEqual(String proof, Node a, Node b, String path) {
        assertEquals(ruleName(a), ruleName(b),
            proof + ": different rule at tree path [" + path + "]");
        assertEquals(position(a), position(b),
            proof + ": rule " + ruleName(a) + " applied at different positions at tree path ["
                + path + "]");
        if (TERM_LEVEL) {
            assertEquals(a.sequent().toString(), b.sequent().toString(),
                proof + ": sequents differ (incl. names) at tree path [" + path + "]");
        }
        assertEquals(a.childrenCount(), b.childrenCount(),
            proof + ": different branching at tree path [" + path + "]");
        for (int i = 0; i < a.childrenCount(); i++) {
            assertTreesEqual(proof, a.child(i), b.child(i),
                path.isEmpty() ? Integer.toString(i) : path + "." + i);
        }
    }

    private static String ruleName(Node n) {
        final RuleApp app = n.getAppliedRuleApp();
        return app == null ? "<none>" : app.rule().name().toString();
    }

    /** Structural, name-independent position: antec/succ + path in the focus term. */
    private static String position(Node n) {
        final RuleApp app = n.getAppliedRuleApp();
        if (app == null || app.posInOccurrence() == null) {
            return "-";
        }
        final PosInOccurrence pio = app.posInOccurrence();
        return (pio.isInAntec() ? "antec " : "succ ") + pio.posInTerm();
    }

    private static KeYEnvironment<?> prove(Path file, int workers) throws Exception {
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsBaseline);
        if (workers == 0) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "false");
        } else {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(workers));
        }
        final KeYEnvironment<?> env = KeYEnvironment.load(file);
        final ProofStarter starter = new ProofStarter(false);
        starter.init(env.getLoadedProof());
        starter.setMaxRuleApplications(MAX_STEPS);
        starter.start();
        return env;
    }
}
