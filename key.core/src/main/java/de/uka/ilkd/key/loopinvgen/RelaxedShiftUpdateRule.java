package de.uka.ilkd.key.loopinvgen;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import org.key_project.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.logic.op.*;

public class RelaxedShiftUpdateRule implements BuiltInRule {

    public final static BuiltInRule RELAXED_SHIFT_RULE = new RelaxedShiftUpdateRule();
    public final static Name RELAXED_SHIFT_UPDATE_NAME = new Name("Relaxed Shift Update");


    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
                                     RuleApp ruleApp) throws RuleAbortException {
        final ImmutableList<Goal> newGoals = goal.split(1);
        final Goal newGoal = newGoals.head();

        RelaxedShiftUpdateImpl worker = new RelaxedShiftUpdateImpl(newGoal);
        worker.shiftUpdate(newGoal, ruleApp.posInOccurrence());

        return newGoals;
    }

    @Override
    public Name name() {
        return RELAXED_SHIFT_UPDATE_NAME;
    }

    @Override
    public String displayName() {
        return RELAXED_SHIFT_UPDATE_NAME.toString();
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        return pio != null && pio.sequentFormula().formula().op() == UpdateApplication.UPDATE_APPLICATION;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
                                     TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

}
