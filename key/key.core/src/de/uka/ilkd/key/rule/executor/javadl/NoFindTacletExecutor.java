package de.uka.ilkd.key.rule.executor.javadl;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

public class NoFindTacletExecutor extends TacletExecutor<NoFindTaclet> {

    public NoFindTacletExecutor(NoFindTaclet taclet) {
        super(taclet);
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * 
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param add
     *           the Sequent to be added
     * @param currentSequent
     *           the Sequent which is the current (intermediate) result of
     *           applying the taclet
     * @param services
     *           the Services encapsulating all java information
     * @param matchCond
     *           the MatchConditions with all required instantiations
     */   
    protected void applyAdd(TermLabelState termLabelState, Sequent add,
            SequentChangeInfo currentSequent, Services services,
            MatchConditions matchCond, Goal goal, RuleApp ruleApp) {
        addToAntec(add.antecedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), currentSequent, null, null, matchCond, goal, ruleApp, services);
        addToSucc(add.succedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), currentSequent, null, null, matchCond, goal, ruleApp, services);
    }    

    /**
     * the rule is applied on the given goal using the
     * information of rule application. 
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the taclet application that is executed
     */
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
        final TermLabelState termLabelState = new TermLabelState();

        // Number without the if-goal eventually needed
        int                          numberOfNewGoals = taclet.goalTemplates().size();

        TacletApp                    tacletApp        = (TacletApp) ruleApp;
        MatchConditions              mc               = tacletApp.matchConditions ();

        ImmutableList<SequentChangeInfo> newSequentsForGoals         =
                checkIfGoals ( goal,
                        tacletApp.ifFormulaInstantiations (),
                        mc,
                        numberOfNewGoals );

        ImmutableList<Goal> newGoals = goal.split(newSequentsForGoals.size());

        Iterator<TacletGoalTemplate> it               = taclet.goalTemplates().iterator();
        Iterator<Goal>               goalIt           = newGoals.iterator();
        Iterator<SequentChangeInfo> newSequentsIt     = newSequentsForGoals.iterator();  

        while (it.hasNext()) {
            TacletGoalTemplate gt          = it    .next();
            Goal               currentGoal = goalIt.next();
            // add first because we want to use pos information that
            // is lost applying replacewith

            SequentChangeInfo currentSequent = newSequentsIt.next();

            applyAdd(   termLabelState,
                    gt.sequent(),
                    currentSequent,
                    services,
                    mc,
                    goal,
                    ruleApp);

            applyAddrule(     gt.rules(),
                    currentGoal,
                    services,
                    mc);

            applyAddProgVars( gt.addedProgVars(),
                    currentSequent,  
                    currentGoal,
                    tacletApp.posInOccurrence(),
                    services,
                    mc);

            currentGoal.setSequent(currentSequent);

            currentGoal.setBranchLabel(gt.name());
            TermLabelManager.refactorSequent(termLabelState, services, ruleApp.posInOccurrence(), ruleApp.rule(), currentGoal, null, null);
        }

        return newGoals;
    }
}
