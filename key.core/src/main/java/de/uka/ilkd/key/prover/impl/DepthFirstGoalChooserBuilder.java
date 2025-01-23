/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.GoalChooserBuilder;

public class DepthFirstGoalChooserBuilder implements GoalChooserBuilder<Proof, Goal> {

    public static final String NAME = "Depth First Goal Chooser";

    public DepthFirstGoalChooserBuilder() {}

    public GoalChooser<Proof, Goal> create() {
        return new DepthFirstGoalChooser();
    }

    public GoalChooserBuilder<Proof, Goal> copy() {
        return new DepthFirstGoalChooserBuilder();
    }

    public String name() {
        return NAME;
    }
}
