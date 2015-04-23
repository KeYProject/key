package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

public class AntecTacletExecutor<TacletKind extends AntecTaclet> 
extends FindTacletExecutor<TacletKind> {


    public AntecTacletExecutor(TacletKind taclet) {
        super(taclet);
    }


    /** CONSTRAINT NOT USED 
     * applies the replacewith part of Taclets
     * @param gt TacletGoalTemplate used to get the replaceexpression in the Taclet
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the taclet
     * @param posOfFind the PosInOccurrence belonging to the find expression
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     * @return 
     */
    @Override
    protected void applyReplacewith(Goal goal, TermLabelState termLabelState, TacletGoalTemplate gt, SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind,
            Services services, 
            MatchConditions matchCond,
            TacletApp tacletApp) {
        if (gt instanceof AntecSuccTacletGoalTemplate) {
            final Sequent replWith = ((AntecSuccTacletGoalTemplate)gt).replaceWith();

            replaceAtPos(termLabelState, replWith.antecedent(), currentSequent, posOfFind, services, matchCond, new TacletLabelHint(TacletOperation.REPLACE_AT_ANTECEDENT, replWith), goal, tacletApp);
            addToSucc(termLabelState, replWith.succedent(), currentSequent, null, services, matchCond, posOfFind, new TacletLabelHint(TacletOperation.REPLACE_TO_SUCCEDENT, replWith), goal, tacletApp);                  
        } else {
            // Then there was no replacewith...
        }
    }


    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param add the Sequent to be added
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the taclet
     * @param posOfFind the PosInOccurrence describes the place where to add
     * the semisequent 
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    @Override
    protected void applyAdd(TermLabelState termLabelState, Sequent add, 
            SequentChangeInfo currentSequent,
            PosInOccurrence posOfFind,
            Services services,
            MatchConditions matchCond,
            Goal goal,
            TacletApp tacletApp) {
        addToAntec(termLabelState, add.antecedent(), currentSequent, posOfFind, services, matchCond, posOfFind, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), goal, tacletApp);
        addToSucc(termLabelState, add.succedent(), currentSequent, null, services, matchCond, posOfFind, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), goal, tacletApp);
    }

}
