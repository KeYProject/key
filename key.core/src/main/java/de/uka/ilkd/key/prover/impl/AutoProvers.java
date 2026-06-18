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
        boolean parallel = ParallelProver.isEnabled() && profile.supportsParallelAutomode();
        return parallel ? new ParallelProver(goalChooser) : new ApplyStrategy(goalChooser);
    }
}
