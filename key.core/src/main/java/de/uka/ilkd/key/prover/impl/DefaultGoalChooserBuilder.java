/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.GoalChooserBuilder;

/**
 * creates the default goal chooser used in KeY
 */
public class DefaultGoalChooserBuilder implements GoalChooserBuilder {

    public static final String NAME = "Simple Goal Chooser";

    public DefaultGoalChooserBuilder() {}

    public GoalChooser create() {
        return new DefaultGoalChooser();
    }

    public String name() {
        return NAME;
    }

    public GoalChooserBuilder copy() {
        return new DefaultGoalChooserBuilder();
    }

}
