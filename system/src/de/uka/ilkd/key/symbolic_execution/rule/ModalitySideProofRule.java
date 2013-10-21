package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;

/**
 * <p>
 * A {@link BuiltInRule} which evaluates a modality in a side proof.
 * </p>
 * <p>
 * This rule is applicable on top level terms ({@link SequentFormula}) of the form. 
 * <ul>
 *    <li>{@code {...}\[...\](<something> = <var>)} or</li>
 *    <li>{@code {...}\<...\>(<something> = <var>)} or</li>
 *    <li>{@code {...}\[...\](<var> = <something>)} or</li>
 *    <li>{@code {...}\<...\>(<var> = <something>)}</li>
 * </ul>
 * The leading updates are optional and any {@link Modality} is supported.
 * </p> 
 * <p>
 * The original {@link SequentFormula} which contains the equality is always
 * removed in the following {@link Goal}. 
 * For each possible result value is a {@link SequentFormula} added to the {@link Sequent} of the form:
 * <ul>
 *    <li>Antecedent: {@code <resultCondition> -> <something> = <result>} or </li>
 *    <li>Antecedent: {@code <resultCondition> -> <result> = <something>} or</li>
 *    <li>Succedent: {@code <resultCondition> & <something> = <result>} or </li>
 *    <li>Succedent: {@code <resultCondition> & <result> = <something>}</li>
 * </ul>
 * The side proof uses the default side proof settings (splitting = delayed) and is started
 * via {@link SymbolicExecutionUtil#startSideProof(de.uka.ilkd.key.proof.Proof, Sequent, String)}.
 * In case that at least one result branch has applicable rules an exception is thrown and the rule is aborted.
 * </p>
 * @author Martin Hentschel
 */
public class ModalitySideProofRule extends AbstractSideProofRule {
   /**
    * The singleton instance of this class.
    */
   public static final ModalitySideProofRule INSTANCE = new ModalitySideProofRule();
   
   /**
    * The {@link Name} of this rule.
    */
   private static final Name NAME = new Name("Evaluate Modality in Side Proof");

   /**
    * Constructor to forbid multiple instances.
    */
   private ModalitySideProofRule() {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isApplicable(Goal goal, PosInOccurrence pio) {
      boolean applicable = false;
      if (pio != null && pio.isTopLevel()) {
         Term term = pio.subTerm();
         term = TermBuilder.DF.goBelowUpdates(term);
         if (term.op() instanceof Modality && SymbolicExecutionUtil.getSymbolicExecutionLabel(term) == null) {
            Term equalityTerm = term.sub(0);
            if (equalityTerm.op() == Equality.EQUALS) {
               if (equalityTerm.sub(0).op() instanceof IProgramVariable ||
                   equalityTerm.sub(1).op() instanceof IProgramVariable) {
                  
                  applicable = true;
               }
            }
         }
      }
      return applicable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBuiltInRuleApp createApp(PosInOccurrence pos) {
      return new DefaultBuiltInRuleApp(this, pos);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
      try {
         // Extract required Terms from goal
         PosInOccurrence pio = ruleApp.posInOccurrence();
         Term topLevelTerm = pio.subTerm();
         Pair<ImmutableList<Term>,Term> updatesAndTerm = TermBuilder.DF.goBelowUpdates2(topLevelTerm);
         Term modalityTerm = updatesAndTerm.second;
         ImmutableList<Term> updates = updatesAndTerm.first;
         Term equalityTerm = modalityTerm.sub(0);
         Term otherTerm;
         Term varTerm;
         boolean varFirst;
         if (equalityTerm.sub(0).op() instanceof LocationVariable) {
            otherTerm = equalityTerm.sub(1);
            varTerm = equalityTerm.sub(0);
            varFirst = true;
         }
         else {
            otherTerm = equalityTerm.sub(0);
            varTerm = equalityTerm.sub(1);
            varFirst = false;
         }
         // Compute sequent for side proof to compute query in.
         Sequent sequentToProve = computeGeneralSequentToProve(goal.sequent(), pio.constrainedFormula());
         Function newPredicate = createResultFunction(services, varTerm.sort());
         Term newTerm = TermBuilder.DF.func(newPredicate, varTerm);
         Term newModalityTerm = TermFactory.DEFAULT.createTerm(modalityTerm.op(), new ImmutableArray<Term>(newTerm), modalityTerm.boundVars(), modalityTerm.javaBlock(), modalityTerm.getLabels());
         Term newModalityWithUpdatesTerm = TermBuilder.DF.applySequential(updates, newModalityTerm);
         sequentToProve = sequentToProve.addFormula(new SequentFormula(newModalityWithUpdatesTerm), false, false).sequent();
         // Compute results and their conditions
         Map<Term, Set<Term>> conditionsAndResultsMap = computeResultsAndConditions(services, goal, sequentToProve, newPredicate);
         // Create new single goal in which the query is replaced by the possible results
         ImmutableList<Goal> goals = goal.split(1);
         Goal resultGoal = goals.head();
         resultGoal.removeFormula(pio);
         for (Entry<Term, Set<Term>> conditionsAndResult : conditionsAndResultsMap.entrySet()) {
            Term conditionTerm = TermBuilder.DF.and(conditionsAndResult.getValue());
            Term resultEqualityTerm = varFirst ?
                                      TermBuilder.DF.equals(conditionsAndResult.getKey(), otherTerm) :
                                      TermBuilder.DF.equals(otherTerm, conditionsAndResult.getKey());
            Term resultTerm = pio.isInAntec() ?
                              TermBuilder.DF.imp(conditionTerm, resultEqualityTerm) :
                              TermBuilder.DF.and(conditionTerm, resultEqualityTerm);
            resultGoal.addFormula(new SequentFormula(resultTerm), pio.isInAntec(), false);
         }
         return goals;
      }
      catch (Exception e) {
         throw new RuleAbortException(e.getMessage());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String displayName() {
      return NAME.toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return displayName();
   }
}
