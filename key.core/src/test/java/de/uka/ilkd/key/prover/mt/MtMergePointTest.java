/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Iterator;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.HelperClassForTests;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.rules.Taclet;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Pins the multi-worker treatment of merge-point statements: with the user preference set to
 * <em>merge</em> ({@code MPS_MERGE}), the merge rule disables itself during a multi-worker run
 * (linking several goals would require synchronizing a subset of goals across workers), and the
 * strategy must then fall back to the safe <em>skip</em> treatment &mdash; deleting merge-point
 * statements &mdash; instead of waiting for a merge that can never happen. Without that fallback
 * every goal reaching a merge point waits forever and the run stalls with the goals stuck there.
 */
public class MtMergePointTest {

    private static final int WORKERS = 2;
    private static final int MAX_STEPS = 20_000;

    /** Snapshot/restore the global settings the example load mutates (sibling-test convention). */
    private static String settingsSnapshot;

    @BeforeAll
    static void snapshotSettings() {
        settingsSnapshot = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    static void restoreSettings() {
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
    }

    @Test
    void mergePointsAreSkippedNotStalledUnderMultiWorkerRun() throws Exception {
        final Path keyFile = HelperClassForTests.TESTCASE_DIRECTORY
                .resolve("merge/gcd.mergePointStatements.key");
        assertTrue(Files.exists(keyFile), () -> "missing test input " + keyFile);

        final String prevEnabled = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String prevThreads = System.getProperty(ParallelProver.THREADS_PROPERTY);
        System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
        System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(WORKERS));
        MtSwitch.assertMultiWorkerActive();
        try {
            ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(settingsSnapshot);
            final KeYEnvironment<?> env = KeYEnvironment.load(keyFile);
            try {
                final Proof proof = env.getLoadedProof();
                final ProofStarter starter = new ProofStarter(false);
                starter.init(proof);
                // The scenario under guard: the user's stored preference is 'merge'.
                final StrategyProperties sp =
                    proof.getSettings().getStrategySettings().getActiveStrategyProperties();
                sp.setProperty(StrategyProperties.MPS_OPTIONS_KEY, StrategyProperties.MPS_MERGE);
                starter.setStrategyProperties(sp);
                starter.setMaxRuleApplications(MAX_STEPS);
                starter.start();

                boolean mergeRuleApplied = false;
                boolean mergePointDeleted = false;
                for (Iterator<Node> it = proof.root().subtreeIterator(); it.hasNext();) {
                    final Node n = it.next();
                    final RuleApp app = n.getAppliedRuleApp();
                    if (app == null) {
                        continue;
                    }
                    if (app instanceof MergeRuleBuiltInRuleApp) {
                        mergeRuleApplied = true;
                    }
                    if (app.rule() instanceof Taclet taclet) {
                        for (RuleSet rs : taclet.getRuleSets()) {
                            if ("merge_point".equals(rs.name().toString())) {
                                mergePointDeleted = true;
                                break;
                            }
                        }
                    }
                }
                assertFalse(mergeRuleApplied,
                    "the merge rule must stay disabled during a multi-worker run");
                assertTrue(mergePointDeleted,
                    "no merge-point statement was deleted: with the 'merge' preference the "
                        + "multi-worker run must fall back to the safe 'skip' treatment, "
                        + "otherwise every goal stalls at its merge point");
            } finally {
                env.dispose();
            }
        } finally {
            restore(ParallelProver.PARALLEL_PROPERTY, prevEnabled);
            restore(ParallelProver.THREADS_PROPERTY, prevThreads);
        }
    }

    private static void restore(String key, String previous) {
        if (previous == null) {
            System.clearProperty(key);
        } else {
            System.setProperty(key, previous);
        }
    }
}
