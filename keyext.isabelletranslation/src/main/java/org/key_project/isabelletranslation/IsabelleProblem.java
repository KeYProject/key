package org.key_project.isabelletranslation;

import de.uka.ilkd.key.proof.Goal;

public class IsabelleProblem {
    private final Goal goal;
    private IsabelleResult result = null;
    private final String preamble;
    private final String sequentTranslation;
    private final String name;

    public IsabelleProblem(Goal goal, String preamble, String sequentTranslation) {
        this.goal = goal;
        this.preamble = preamble;
        this.sequentTranslation = sequentTranslation;
        this.name = "Goal " + goal.node().serialNr();
    }

    public Goal getGoal() {
        return goal;
    }

    public String getSequentTranslation() {
        return sequentTranslation;
    }

    public String getPreamble() {
        return preamble;
    }

    public String getName() {
        return name;
    }

    public IsabelleResult getResult() {
        return result;
    }

    protected void setResult(IsabelleResult result) {
        this.result = result;
    }
}
