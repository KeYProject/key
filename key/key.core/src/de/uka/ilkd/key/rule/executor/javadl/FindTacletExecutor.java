package de.uka.ilkd.key.rule.executor.javadl;

import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.label.TermLabelManager;
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


    /**  
     * applies the {@code replacewith}-expression of taclet goal descriptions
     * @param gt the {@link TacletGoalTemplate} used to get the taclet's {@code replacewith}-expression 
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate) result of applying the taclet
     * @param posOfFind the {@link PosInOccurrence} belonging to the find expression
     * @param matchCond the {@link MatchConditions} with all required instantiations 
     * @param goal the {@link Goal} on which the taclet is applied 
     * @param ruleApp the {@link TacletApp} describing the current ongoing taclet application
     * @param services the {@link Services} encapsulating all Java model information
     */
    protected abstract void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState, 
                         SequentChangeInfo currentSequent, PosInOccurrence posOfFind,
                         MatchConditions matchCond,
                         Goal goal,
                         RuleApp ruleApp,
                         Services services);


    /**
     * applies the {@code add}-expressions of taclet goal descriptions
     * @param add the {@link Sequent} with the uninstantiated {@link SequentFormula}'s to be added to the goal's sequent
     * @param termLabelState The {@link TermLabelState} of the current rule application.
     * @param currentSequent the {@link SequentChangeInfo} which is the current (intermediate) result of applying the taclet
     * @param posOfFind the {@link PosInOccurrence} providing the position information where the match took place 
     * (it will be tried to add the new formulas close to that position)
     * @param matchCond the {@link MatchConditions} with all required instantiations 
     * @param ruleApp the {@link TacletApp} describing the current ongoing taclet application
     * @param services the {@link Services} encapsulating all Java model information
     */
    protected abstract void applyAdd(Sequent add, TermLabelState termLabelState, SequentChangeInfo currentSequent,
                     PosInOccurrence posOfFind,
                     MatchConditions matchCond,
                     Goal goal,
                     RuleApp ruleApp,
                     Services services);


    
    /**  
     * the rule is applied on the given goal using the
     * information of rule application. 
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the taclet application that is executed.
     */
    public final ImmutableList<Goal> apply(Goal     goal,
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
        
        applyAdd(gt.sequent(), termLabelState,
                  currentSequent,
                  tacletApp.posInOccurrence(),
                  mc,
                  goal,
                  ruleApp,
                  services);

        applyReplacewith(gt, 
                 termLabelState, currentSequent,
                 tacletApp.posInOccurrence(),
                 mc,
                 currentGoal,
                 ruleApp,
                 services);

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
       
       TermLabelManager.refactorSequent(termLabelState, services, ruleApp.posInOccurrence(), ruleApp.rule(), currentGoal, null, null);
    }
    
    // in case the assumes sequent of the taclet did not
    // already occur in the goal sequent, we had to perform a cut
    // in this loop we make sure to assign the cut goal its correct
    // sequent
    while (newSequentsIt.hasNext()) {
       Goal nextGoal = goalIt.next();
       nextGoal.setSequent(newSequentsIt.next());
       TermLabelManager.refactorGoal(termLabelState, services, ruleApp.posInOccurrence(), ruleApp.rule(), nextGoal, null, null);
    }
    
    assert !goalIt.hasNext();

    return newGoals;
    }
}
