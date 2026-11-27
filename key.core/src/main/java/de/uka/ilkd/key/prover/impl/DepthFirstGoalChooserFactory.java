/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.GoalChooserFactory;

public class DepthFirstGoalChooserFactory implements GoalChooserFactory<Goal> {

    public static final String NAME = "Depth First Goal Chooser";

    public DepthFirstGoalChooserFactory() {}

    public GoalChooser<Goal> create() {
        return new DepthFirstGoalChooser();
    }

    public GoalChooserFactory<Goal> copy() {
        return new DepthFirstGoalChooserFactory();
    }

    public String name() {
        return NAME;
    }
}
