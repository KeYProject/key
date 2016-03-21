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
import de.uka.ilkd.key.rule.RuleApp;
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
    private Term replace(Term term,
            Term with,
            TermLabelState termLabelState,
            TacletLabelHint labelHint,
            PosInOccurrence posOfFind,
            IntIterator it,
            MatchConditions mc,
            Sort maxSort,
            Goal goal,
            Services services,
            RuleApp ruleApp) {
        if (it.hasNext()) {
            final int indexOfNextSubTerm = it.next();

            final Term[] subs = new Term[term.arity()];
            term.subs().arraycopy(0, subs, 0, term.arity());

            final Sort newMaxSort = TermHelper.getMaxSort(term, indexOfNextSubTerm, services);
            subs[indexOfNextSubTerm] = replace(term.sub(indexOfNextSubTerm), with,
                    termLabelState,
                    labelHint,
                    posOfFind,
                    it,
                    mc,
                    newMaxSort,
                    goal,
                    services, 
                    ruleApp);            

            return services.getTermFactory().createTerm(term.op(),
                    subs,
                    term.boundVars(),
                    term.javaBlock(),
                    term.getLabels());
        }

        with = syntacticalReplace(with, termLabelState, labelHint, posOfFind, mc, goal, ruleApp, services);

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
                    RuleApp ruleApp) {
    final Term term = posOfFind.sequentFormula().formula();
    final IntIterator it = posOfFind.posInTerm().iterator();
    final Term rwTemplate = gt.replaceWith();

    Term formula = replace(term,
                           rwTemplate,
                           termLabelState,
                           new TacletLabelHint(rwTemplate),
                           posOfFind,
                           it,
                           matchCond,
                           term.sort(),
                           goal,
                           services,
                           ruleApp);
    formula = TermLabelManager.refactorSequentFormula(termLabelState, services, formula, posOfFind, taclet, goal, null, rwTemplate);
    if(term == formula) {
        return posOfFind.sequentFormula();
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
     * {@inheritDoc}
     */
   @Override
   protected void applyReplacewith(TacletGoalTemplate gt, TermLabelState termLabelState, 
           SequentChangeInfo currentSequent, PosInOccurrence posOfFind,
           MatchConditions matchCond,
           Goal goal,
           RuleApp ruleApp,
           Services services) {
      if (gt instanceof RewriteTacletGoalTemplate) {
         SequentFormula cf = applyReplacewithHelper(goal, termLabelState,
               (RewriteTacletGoalTemplate) gt, posOfFind, services, matchCond, ruleApp);

         currentSequent.combine(currentSequent.sequent().changeFormula(cf, posOfFind));
      }
      else {
         // Then there was no replacewith...
         // This is strange in a RewriteTaclet, but who knows...
         // However, term label refactorings have to be performed.
         Term oldFormula = posOfFind.sequentFormula().formula();
         Term newFormula = TermLabelManager.refactorSequentFormula(termLabelState, services, oldFormula, 
                 posOfFind, taclet, goal, null, null);
         if (oldFormula != newFormula) {
            currentSequent.combine(currentSequent.sequent().changeFormula(new SequentFormula(newFormula), posOfFind));
         }
      }
   }

   /**
    * adds the sequent of the add part of the Taclet to the goal sequent
 * @param add
    *           the Sequent to be added
 * @param termLabelState The {@link TermLabelState} of the current rule application.
 * @param currentSequent
    *           the Sequent which is the current (intermediate) result of
    *           applying the taclet
 * @param posOfFind
    *           the PosInOccurrence describes the place where to add the
    *           semisequent
 * @param matchCond
    *           the MatchConditions with all required instantiations
 * @param services
    *           the Services encapsulating all java information
    */
   @Override
   protected void applyAdd(Sequent add, TermLabelState termLabelState,
         SequentChangeInfo currentSequent, PosInOccurrence posOfFind,
         MatchConditions matchCond, Goal goal, RuleApp ruleApp, Services services) {
      if (posOfFind.isInAntec()) {
         addToAntec(add.antecedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), currentSequent, posOfFind, posOfFind, matchCond, goal, ruleApp, services);
         addToSucc(add.succedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), currentSequent, null, posOfFind, matchCond, goal, ruleApp, services);
      }
      else {
         addToAntec(add.antecedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add), currentSequent, null, posOfFind, matchCond, goal, ruleApp, services);
         addToSucc(add.succedent(), termLabelState, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add), currentSequent, posOfFind, posOfFind, matchCond, goal, ruleApp, services);
      }
   }
}
