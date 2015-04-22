package de.uka.ilkd.key.rule.executor.javadl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.util.TermHelper;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

public class RewriteTacletExecutor<TacletKind extends RewriteTaclet> extends FindTacletExecutor<TacletKind> {

    public RewriteTacletExecutor(TacletKind taclet) {
        super(taclet);
    }

    
    /**
     * does the work for applyReplacewith (wraps recursion) 
     */
    private Term replace(TermLabelState termLabelState,
                         Term term,
                         Term with,
                         PosInOccurrence posOfFind,
                         IntIterator it,
                         Services services,
                         MatchConditions mc,
                         Sort maxSort,
                         TacletLabelHint labelHint,
                         Goal goal,
                         TacletApp tacletApp) {
    if (it.hasNext()) {
        int sub = it.next();

        final Term[] subs = new Term[term.arity()];

        for (int i=0, arity = term.arity(); i<arity; i++) {

                if (i!=sub) {
            subs[i] = term.sub(i);
        } else {
                    final Sort newMaxSort = TermHelper.getMaxSort(term, i, services);
            subs[i] = replace(termLabelState, term.sub(i),
                      with,
                          posOfFind,
                      it,
                      services,
                      mc,
                          newMaxSort,
                         labelHint,
                         goal, 
                         tacletApp);
        }
        }

        return services.getTermFactory().createTerm(term.op(),
                                                  subs,
                                                  term.boundVars(),
                                                  term.javaBlock(),
                                  term.getLabels());
    }

    with = syntacticalReplace(termLabelState, with, services, mc, posOfFind, labelHint, goal, tacletApp);

    if(!with.sort().extendsTrans(maxSort)) {
        with = services.getTermBuilder().cast(maxSort, with);
    }

    return with;
    }


    private SequentFormula applyReplacewithHelper(Goal goal,
               TermLabelState termLabelState, 
                    RewriteTacletGoalTemplate gt, 
                    PosInOccurrence    posOfFind,
                    Services           services,
                    MatchConditions    matchCond,
                    TacletApp tacletApp) {
    Term term = posOfFind.constrainedFormula().formula();
    IntIterator it = posOfFind.posInTerm().iterator();
    Term rwTemplate=gt.replaceWith();

    Term formula = replace(termLabelState,
                           term,
                           rwTemplate,
                           posOfFind,
                           it,
                           services,
                           matchCond,
                           term.sort(),
                           new TacletLabelHint(rwTemplate),
                           goal,
                           tacletApp);
    formula = TermLabelManager.refactorSequentFormula(termLabelState, services, formula, posOfFind, taclet, goal, null, rwTemplate);
    if(term == formula) {
        return posOfFind.constrainedFormula();
    } else {
        return new SequentFormula(formula);
    }
    }
    
    
    public SequentFormula getRewriteResult(Goal goal, TermLabelState termLabelState, Services services, TacletApp app) {
        assert taclet.goalTemplates().size() == 1;
        assert taclet.goalTemplates().head().sequent().isEmpty();  
        assert taclet.getApplicationRestriction() != RewriteTaclet.IN_SEQUENT_STATE;
        assert app.complete();
        RewriteTacletGoalTemplate gt 
        = (RewriteTacletGoalTemplate) taclet.goalTemplates().head();
        return applyReplacewithHelper(goal, termLabelState,
                gt,
                app.posInOccurrence(),
                services,
                app.matchConditions(),
                app);
    }


    /** 
     * applies the replacewith part of Taclets
     * @param gt TacletGoalTemplate used to get the replaceexpression in the Taclet
     * @param currentSequent
     *           the Sequent which is the current (intermediate) result of
     *           applying the taclet
     * @param posOfFind the PosInOccurrence belonging to the find expression
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
   @Override
   protected void applyReplacewith(Goal goal, TermLabelState termLabelState, TacletGoalTemplate gt,
         SequentChangeInfo currentSequent, PosInOccurrence posOfFind,
         Services services, MatchConditions matchCond, TacletApp tacletApp) {
      if (gt instanceof RewriteTacletGoalTemplate) {
         SequentFormula cf = applyReplacewithHelper(goal, termLabelState,
               (RewriteTacletGoalTemplate) gt, posOfFind, services, matchCond, tacletApp);

         currentSequent.combine(currentSequent.sequent().changeFormula(cf, posOfFind));
      }
      else {
         // Then there was no replacewith...
         // This is strange in a RewriteTaclet, but who knows...
         // However, term label refactorings have to be performed.
         Term oldFormula = posOfFind.constrainedFormula().formula();
         Term newFormula = TermLabelManager.refactorSequentFormula(termLabelState, services, oldFormula, posOfFind, taclet, goal, null, null);
         if (oldFormula != newFormula) {
            currentSequent.combine(currentSequent.sequent().changeFormula(new SequentFormula(newFormula), posOfFind));
         }
      }
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
    * @param posOfFind
    *           the PosInOccurrence describes the place where to add the
    *           semisequent
    * @param services
    *           the Services encapsulating all java information
    * @param matchCond
    *           the MatchConditions with all required instantiations
    */
   @Override
   protected void applyAdd(TermLabelState termLabelState, Sequent add,
         SequentChangeInfo currentSequent, PosInOccurrence posOfFind,
         Services services, MatchConditions matchCond, Goal goal, TacletApp tacletApp) {
      if (posOfFind.isInAntec()) {
         addToAntec(termLabelState, add.antecedent(), currentSequent, posOfFind, services, matchCond, posOfFind, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), goal, tacletApp);
         addToSucc(termLabelState, add.succedent(), currentSequent, null, services, matchCond, posOfFind, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), goal, tacletApp);
      }
      else {
         addToAntec(termLabelState, add.antecedent(), currentSequent, null, services, matchCond, posOfFind, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), goal, tacletApp);
         addToSucc(termLabelState, add.succedent(), currentSequent, posOfFind, services, matchCond, posOfFind, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), goal, tacletApp);
      }
   }
}
