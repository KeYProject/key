/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.GoalChooserBuilder;

public class DepthFirstGoalChooserBuilder implements GoalChooserBuilder {

    public static final String NAME = "Depth First Goal Chooser";

    public DepthFirstGoalChooserBuilder() {}

    public GoalChooser create() {
        return new DepthFirstGoalChooser();
    }

    public GoalChooserBuilder copy() {
        return new DepthFirstGoalChooserBuilder();
    }

    public String name() {
        return NAME;
    }
}
