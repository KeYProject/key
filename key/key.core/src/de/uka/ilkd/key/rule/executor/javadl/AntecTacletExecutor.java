package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

public class AntecTacletExecutor<TacletKind extends AntecTaclet> 
extends FindTacletExecutor<TacletKind> {


    public AntecTacletExecutor(TacletKind taclet) {
        super(taclet);
    }


    /**  
     * {@inheritDoc}
     */
    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState, SequentChangeInfo currentSequent, PosInOccurrence posOfFind,
            MatchConditions matchCond,
            Goal goal, 
            RuleApp ruleApp,
            Services services) {
        if (gt instanceof AntecSuccTacletGoalTemplate) {
            final Sequent replWith = ((AntecSuccTacletGoalTemplate)gt).replaceWith();
            replaceAtPos(replWith.antecedent(), termLabelState, currentSequent, posOfFind, matchCond, 
                    new TacletLabelHint(TacletOperation.REPLACE_AT_ANTECEDENT, replWith), goal, 
                    ruleApp, services);
            if (!replWith.succedent().isEmpty()) {
                addToSucc(replWith.succedent(), termLabelState, new TacletLabelHint(TacletOperation.REPLACE_TO_SUCCEDENT, replWith), currentSequent, null, 
                        posOfFind, matchCond, goal, 
                        ruleApp, services);                  
            }
        } else {
            // Then there was no replacewith...
        }
    }


    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * @param add the Sequent to be added
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the taclet
     * @param posOfFind the PosInOccurrence describes the place where to add
     * the semisequent 
     * @param matchCond the MatchConditions with all required instantiations 
     * @param services the Services encapsulating all java information
     */
    @Override
    protected void applyAdd(Sequent add, TermLabelState termLabelState, 
            SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind,
            MatchConditions matchCond,
            Goal goal,
            RuleApp ruleApp,
            Services services) {
        addToAntec(add.antecedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), currentSequent, posOfFind, posOfFind, matchCond, goal, ruleApp, services);
        addToSucc(add.succedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), currentSequent, null, posOfFind, matchCond, goal, ruleApp, services);
    }

}
