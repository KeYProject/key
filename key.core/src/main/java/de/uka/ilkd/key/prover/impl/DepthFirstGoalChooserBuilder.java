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
