/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.GoalChooserFactory;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class DepthFirstGoalChooserFactory implements GoalChooserFactory<Proof, Goal> {

    public static final String NAME = "Depth First Goal Chooser";

    public DepthFirstGoalChooserFactory() {}

    /**
     * The concrete chooser binds its type parameters to {@code @Nullable} (generic-bound artifact
     * of the {@code GoalChooser} interface), which is incompatible with the factory's
     * {@code @NonNull} parameter binding; the chooser never observes null proofs or goals, so the
     * difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:return.type.incompatible")
    public GoalChooser<Proof, Goal> create() {
        return new DepthFirstGoalChooser();
    }

    public GoalChooserFactory<Proof, Goal> copy() {
        return new DepthFirstGoalChooserFactory();
    }

    public String name() {
        return NAME;
    }
}
