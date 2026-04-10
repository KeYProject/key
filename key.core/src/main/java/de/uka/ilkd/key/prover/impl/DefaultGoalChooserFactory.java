/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.GoalChooserFactory;

/**
 * creates the default goal chooser used in KeY
 */
public class DefaultGoalChooserFactory implements GoalChooserFactory<Proof, Goal> {

    public static final String NAME = "Simple Goal Chooser";

    public DefaultGoalChooserFactory() {}

    public GoalChooser<Proof, Goal> create() {
        return new DefaultGoalChooser();
    }

    public String name() {
        return NAME;
    }

    public GoalChooserFactory<Proof, Goal> copy() {
        return new DefaultGoalChooserFactory();
    }

}
