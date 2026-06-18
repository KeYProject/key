/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.Profile;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.ProverCore;

/**
 * Selection seam for the prover used by automatic proof search.
 *
 * <p>
 * Returns the {@link ParallelProver} when the multi-core prover is enabled <em>and</em> the proof's
 * {@link Profile#supportsParallelAutomode() profile supports it}, and the standard single-threaded
 * {@link ApplyStrategy} otherwise. Construction sites that drive automode should go through here
 * instead of constructing {@link ApplyStrategy} directly, so the parallel path can be toggled
 * centrally and the profile guard cannot be bypassed.
 *
 * @author Claude (KeY multithreading effort)
 */
public final class AutoProvers {

    private AutoProvers() {}

    /**
     * Creates the auto-prover selected by the current configuration for the given profile.
     *
     * @param goalChooser the goal chooser to use
     * @param profile the profile of the proof to be processed; the parallel prover is used only if
     *        it {@link Profile#supportsParallelAutomode() supports parallel automode}
     * @return a {@link ParallelProver} if enabled and supported, otherwise an {@link ApplyStrategy}
     */
    public static ProverCore<Proof, Goal> create(GoalChooser<Proof, Goal> goalChooser,
            Profile profile) {
        return create(goalChooser, profile, true);
    }

    /**
     * Creates the auto-prover selected by the current configuration, optionally forcing the
     * single-threaded prover.
     *
     * <p>
     * {@code allowParallel == false} pins the run to {@link ApplyStrategy} even when the multi-core
     * prover is enabled. This is for drivers that close one goal at a time under a tight per-goal
     * step budget (notably {@link de.uka.ilkd.key.macros.TryCloseMacro}): there is no parallelism
     * to
     * gain from a single goal, and several workers exploring one goal's subtree apply rules in a
     * different, less step-efficient order than the single-threaded prover -- which can exhaust the
     * budget before the goal closes. The wide, generously-budgeted runs (interactive automode and
     * most macros) keep using the parallel prover, where it pays off.
     *
     * @param goalChooser the goal chooser to use
     * @param profile the profile of the proof to be processed
     * @param allowParallel whether the parallel prover may be used at all for this run
     * @return a {@link ParallelProver} if allowed, enabled and supported, otherwise an
     *         {@link ApplyStrategy}
     */
    public static ProverCore<Proof, Goal> create(GoalChooser<Proof, Goal> goalChooser,
            Profile profile, boolean allowParallel) {
        boolean parallel =
            allowParallel && ParallelProver.isEnabled() && profile.supportsParallelAutomode();
        return parallel ? new ParallelProver(goalChooser) : new ApplyStrategy(goalChooser);
    }
}
