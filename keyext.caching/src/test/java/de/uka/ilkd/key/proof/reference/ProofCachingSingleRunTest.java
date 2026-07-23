/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.reference;

import java.nio.file.Path;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppListener;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.settings.GeneralSettings;

import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Regression test for the proof-caching "search stops, restart needed" bug: a single automatic
 * run followed by the caching close step must finish the proof, rather than stranding an enabled
 * goal and requiring the user to restart.
 *
 * <p>
 * The scenario mirrors what {@code CachingExtension} does in the GUI: while proving a second copy
 * of a proof, goals that can be closed by reference to the first (closed) proof are disabled during
 * the run and closed once it finishes. With the
 * {@link de.uka.ilkd.key.prover.impl.DepthFirstGoalChooser}
 * loss-recovery in place, disabling those sibling goals around a branching rule no longer drops an
 * unrelated enabled goal from the work lists, so the proof closes in one pass.
 */
class ProofCachingSingleRunTest {
    private static final Path testCaseDirectory =
        Objects.requireNonNull(FindResources.getTestCasesDirectory());
    private static final Path BIN = testCaseDirectory.resolve(
        "../../../../../key.ui/examples/heap/WeideEtAl_02_BinarySearch/BinarySearch_search.key");

    private static ApplyStrategyInfo<Proof, Goal> auto(Proof p, ImmutableList<Goal> goals) {
        int maxSteps = p.getSettings().getStrategySettings().getMaxSteps();
        long timeout = p.getSettings().getStrategySettings().getTimeout();
        ApplyStrategy s = new ApplyStrategy(
            p.getInitConfig().getProfile().<Proof, Goal>getSelectedGoalChooserBuilder().create());
        return s.start(p, goals, maxSteps, timeout, false);
    }

    @Test
    void cachingClosesInASingleRun() throws Exception {
        GeneralSettings.noPruningClosed = false;
        KeYEnvironment<DefaultUserInterfaceControl> e1 = KeYEnvironment.load(BIN);
        Proof src = e1.getLoadedProof();
        KeYEnvironment<DefaultUserInterfaceControl> e2 = KeYEnvironment.load(BIN);
        Proof p2 = e2.getLoadedProof();
        try {
            auto(src, src.openEnabledGoals());
            assertTrue(src.closed(), "cache source proof must close");

            List<Proof> previous = new CopyOnWriteArrayList<>();
            previous.add(src);
            int[] disables = { 0 };
            // mirror CachingExtension.ruleApplied: disable cache-hit new goals of a split
            RuleAppListener caching = ev -> {
                ImmutableList<Goal> ng = ev.getNewGoals();
                if (ng.size() <= 1) {
                    return;
                }
                for (Goal g : ng) {
                    ClosedBy c = null;
                    try {
                        c = ReferenceSearcher.findPreviousProof(previous, g.node());
                    } catch (Exception ignore) {
                        // reference search failure -> just do not cache this goal
                    }
                    if (c != null) {
                        g.setEnabled(false);
                        g.node().register(c, ClosedBy.class);
                        disables[0]++;
                    }
                }
            };
            p2.addRuleAppListener(caching);

            // exactly one automatic run ...
            auto(p2, p2.openEnabledGoals());
            // ... then the caching close step (mirror CachingExtension.taskFinished)
            p2.openGoals().stream().filter(g -> g.node().lookup(ClosedBy.class) != null)
                    .collect(Collectors.toList()).forEach(g -> {
                        g.setEnabled(true);
                        p2.closeGoal(g);
                    });

            assertTrue(disables[0] > 0, "the caching scenario must actually disable some goals");
            assertTrue(p2.closed(),
                "proof must close in a single run; a stranded enabled goal here is the "
                    + "'caching stops the search, restart needed' bug");
        } finally {
            GeneralSettings.noPruningClosed = true;
            src.dispose();
            p2.dispose();
        }
    }
}
