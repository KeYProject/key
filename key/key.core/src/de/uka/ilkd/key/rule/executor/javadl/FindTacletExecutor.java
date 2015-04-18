package de.uka.ilkd.key.rule.executor.javadl;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

public abstract class FindTacletExecutor<TacletKind extends FindTaclet> extends TacletExecutor<TacletKind> {
    
    
    public FindTacletExecutor(TacletKind taclet) {
        super(taclet);
    }


    /** CONSTRAINT NOT USED 
     * applies the replacewith part of Taclets
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param gt TacletGoalTemplate used to get the replaceexpression 
     * in the Taclet
     * @param currentSequent the Sequent which is the current (intermediate) result of applying the taclet
     * @param posOfFind the PosInOccurrence belonging to the find expression
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected abstract void applyReplacewith(Goal goal, TermLabelState termLabelState, 
                         TacletGoalTemplate gt, SequentChangeInfo currentSequent,
                         PosInOccurrence posOfFind,
                         Services services,
                         MatchConditions matchCond,
                         TacletApp tacletApp);


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
    protected abstract void applyAdd(TermLabelState termLabelState, Sequent add, SequentChangeInfo sequentChangeInfo,
                     PosInOccurrence posOfFind,
                     Services services,
                     MatchConditions matchCond,
                     Goal goal,
                     TacletApp tacletApp);


    
    /**  
     * the rule is applied on the given goal using the
     * information of rule application. 
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the taclet application that is executed.
     */
    public ImmutableList<Goal> apply(Goal     goal,
                Services services,
                RuleApp  ruleApp) {
   final TermLabelState termLabelState = new TermLabelState();
    // Number without the if-goal eventually needed
    int                          numberOfNewGoals = taclet.goalTemplates().size();

    TacletApp                    tacletApp        = (TacletApp) ruleApp;
    MatchConditions              mc               = tacletApp.matchConditions ();

    ImmutableList<SequentChangeInfo>                   newSequentsForGoals         =
        checkIfGoals ( goal,
               tacletApp.ifFormulaInstantiations (),
               mc,
               numberOfNewGoals );
    
    ImmutableList<Goal> newGoals = goal.split(newSequentsForGoals.size());
    
    Iterator<TacletGoalTemplate> it               = taclet.goalTemplates().iterator(); 
    Iterator<Goal>               goalIt           = newGoals.iterator();
   Iterator<SequentChangeInfo> newSequentsIt = newSequentsForGoals.iterator();

    while (it.hasNext()) {
        TacletGoalTemplate gt          = it    .next();
        Goal               currentGoal = goalIt.next();
       SequentChangeInfo  currentSequent = newSequentsIt.next();

        // add first because we want to use pos information that
        // is lost applying replacewith
        
        applyAdd(termLabelState, gt.sequent(),
                  currentSequent,
                  tacletApp.posInOccurrence(),
                  services,
                  mc,
                  goal,
                  (TacletApp) ruleApp);

        applyReplacewith(currentGoal, 
                 termLabelState, gt,
                 currentSequent,
                 tacletApp.posInOccurrence(),
                 services,
                 mc,
                 (TacletApp) ruleApp);

        applyAddrule( gt.rules(),
                  currentGoal,
                  services,
                  mc );

        
        applyAddProgVars( gt.addedProgVars(),
                currentSequent,
                  currentGoal,
               tacletApp.posInOccurrence(),
               services,
                  mc);
                               
       currentGoal.setSequent(currentSequent);              
        
       currentGoal.setBranchLabel(gt.name());
    }
    
    // in case the assumes sequent of the taclet did not
    // already occur in the goal sequent, we had to perform a cut
    // in this loop we make sure to assign the cut goal its correct
    // sequent
    while (newSequentsIt.hasNext()) {
       goalIt.next().setSequent(newSequentsIt.next());
    }
    
    assert !goalIt.hasNext();

    return newGoals;
    }
}
