package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

public class SuccTacletExecutor<TacletKind extends SuccTaclet> extends FindTacletExecutor<TacletKind> {

    public SuccTacletExecutor(TacletKind taclet) {
        super(taclet);
    }

    /** 
     * {@inheritDoc}
     */
    @Override
    protected void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState, 
            SequentChangeInfo currentSequent, PosInOccurrence posOfFind,
            MatchConditions matchCond,
            Goal goal,
            RuleApp ruleApp,
            Services services) {
        if (gt instanceof AntecSuccTacletGoalTemplate) {
            final Sequent replWith = ((AntecSuccTacletGoalTemplate)gt).replaceWith();

            replaceAtPos(replWith.succedent(), termLabelState, currentSequent, posOfFind, matchCond, 
                    new TacletLabelHint(TacletOperation.REPLACE_AT_SUCCEDENT, replWith), goal, ruleApp, services);
            if (!replWith.antecedent().isEmpty()) {
                addToAntec(replWith.antecedent(), termLabelState, new TacletLabelHint(TacletOperation.REPLACE_TO_ANTECEDENT, replWith), currentSequent, null, posOfFind, matchCond, 
                        goal, 
                        ruleApp, services);
            }
        } 
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void applyAdd(Sequent add, TermLabelState termLabelState, 
            SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind,
            MatchConditions matchCond,
            Goal goal,
            RuleApp ruleApp,
            Services services) {
        addToAntec(add.antecedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), currentSequent, null, posOfFind, matchCond, goal, ruleApp, services);
        addToSucc(add.succedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), currentSequent, posOfFind, posOfFind, matchCond, goal, ruleApp, services);
    }
}
