// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Triple;

/**
 * <p>
 * A {@link BuiltInRule} which evaluates a query in a side proof.
 * </p>
 * <p>
 * This rule is applicable on each equality which contains a query: 
 * <ul>
 *    <li>{@code ...(<something> = <query>)...} or</li>
 *    <li>{@code ...(<query> = <something>)...}</li>
 * </ul>
 * </p>
 * <p>
 * The original {@link SequentFormula} which contains the equality is always
 * removed in the following {@link Goal}. How the result of the query computed
 * in the side proof is represented depends on the occurrence of the equality:
 * <ol>
 *    <li>
 *       <b>top level {@code <something> = <query>} or {@code <query> = <something>}</b><br>
 *       For each possible result value is a {@link SequentFormula} added to the {@link Sequent} of the form:
 *       <ul>
 *          <li>Antecedent: {@code <resultCondition> -> <something> = <result>} or </li>
 *          <li>Antecedent: {@code <resultCondition> -> <result> = <something>} or</li>
 *          <li>Succedent: {@code <resultCondition> & <something> = <result>} or </li>
 *          <li>Succedent: {@code <resultCondition> & <result> = <something>}</li>
 *       </ul>
 *    </li>
 *    <li>
 *       <b>right side of an implication on top level {@code <queryCondition> -> <something> = <query>} or {@code <queryCondition> -> <query> = <something>}</b><br>
 *       For each possible result value is a {@link SequentFormula} added to the {@link Sequent} of the form:
 *       <ul>
 *          <li>Antecedent: {@code <pre> -> (<resultCondition> -> <something> = <result>)} or </li>
 *          <li>Antecedent: {@code <pre> -> (<resultCondition> -> <result> = <something>)} or</li>
 *          <li>Succedent: {@code <pre> -> (<resultCondition> & <something> = <result>)} or </li>
 *          <li>Succedent: {@code <pre> -> (<resultCondition> & <result> = <something>)}</li>
 *       </ul>
 *    </li>
 *    <li>
 *       <b>everywhere else {@code ...(<something> = <query>)...} or {@code ...(<query> = <something>)...}</b><br>
 *       In the original {@link SequentFormula} is the {@code <query>} replaced by a new constant function named {@code QueryResult} and added to the antecedent/succedent in which it was contained before.
 *       For each possible result value is an additional {@link SequentFormula} added to the <b>antecedent</b> of the form:
 *       <ul>
 *          <li>{@code <resultCondition> -> QueryResult = <result>} or </li>
 *          <li>{@code <resultCondition> -> <result> = QueryResult}</li>
 *       </ul>
 *    </li>
 * </ol>
 * The side proof uses the default side proof settings (splitting = delayed) and is started
 * via {@link SymbolicExecutionUtil#startSideProof(de.uka.ilkd.key.proof.Proof, Sequent, String)}.
 * In case that at least one result branch has applicable rules an exception is thrown and the rule is aborted.
 * </p>
 * @author Martin Hentschel
 */
public final class QuerySideProofRule extends AbstractSideProofRule {
   /**
    * The singleton instance of this class.
    */
   public static final QuerySideProofRule INSTANCE = new QuerySideProofRule();
   
   /**
    * The {@link Name} of this rule.
    */
   private static final Name NAME = new Name("Evaluate Query in Side Proof");

   /**
    * Constructor to forbid multiple instances.
    */
   private QuerySideProofRule() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isApplicable(Goal goal, PosInOccurrence pio) {
      boolean applicable = false;
      if (pio != null) {
          // abort if inside of transformer
          if (Transformer.inTransformer(pio)) {
              return false;
          }
         Term term = pio.subTerm();
         if (term != null) {
            if (term.op() == Equality.EQUALS) {
               applicable = isApplicableQuery(goal, term.sub(0), pio) ||
                            isApplicableQuery(goal, term.sub(1), pio);
            }
         }
      }
      return applicable;
   }
   
   /**
    * Checks if the query term is supported. The functionality is identical to
    * {@link QueryExpand#isApplicable(Goal, PosInOccurrence)}.
    * @param goal The {@link Goal}.
    * @param pmTerm The {@link Term} to with the query to check.
    * @param pio The {@link PosInOccurrence} in the {@link Goal}.
    * @return {@code true} is applicable, {@code false} is not applicable
    */
   protected boolean isApplicableQuery(Goal goal, Term pmTerm, PosInOccurrence pio) {
      if (pmTerm.op() instanceof IProgramMethod && pmTerm.freeVars().isEmpty()) {
         IProgramMethod pm = (IProgramMethod) pmTerm.op();
         final Sort nullSort = goal.proof().getJavaInfo().nullSort();
         if (pm.isStatic() || (pmTerm.sub(1).sort().extendsTrans(goal.proof().getJavaInfo().objectSort()) &&
                 !pmTerm.sub(1).sort().extendsTrans(nullSort))) {
             PIOPathIterator it = pio.iterator();
             while ( it.next() != -1 ) {
                 Term focus = it.getSubTerm();
                 if (focus.op() instanceof UpdateApplication || focus.op() instanceof Modality) {
                     return false;
                 }
             }
             return true;
         }
     }
     return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
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
         Sequent goalSequent = goal.sequent();
         SequentFormula equalitySF = pio.constrainedFormula();
         Term equalityTerm = pio.subTerm();
         Term queryTerm;
         Term varTerm;
         boolean varFirst;
         if (equalityTerm.sub(0).op() instanceof LocationVariable) {
            queryTerm = equalityTerm.sub(1);
            varTerm = equalityTerm.sub(0);
            varFirst = true;
         }
         else {
            queryTerm = equalityTerm.sub(0);
            varTerm = equalityTerm.sub(1);
            varFirst = false;
         }
         Term queryConditionTerm = null;
         if (equalitySF.formula().op() == Junctor.IMP && equalitySF.formula().sub(1) == equalityTerm) {
            queryConditionTerm = equalitySF.formula().sub(0); 
         }
         // Compute sequent for side proof to compute query in.
         final ProofEnvironment sideProofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(goal.proof(), true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
         final Services sideProofServices = sideProofEnv.getServicesForEnvironment();
         Sequent sequentToProve = SideProofUtil.computeGeneralSequentToProve(goalSequent, equalitySF);
         Function newPredicate = createResultFunction(sideProofServices, queryTerm.sort());
         Term newTerm = sideProofServices.getTermBuilder().func(newPredicate, queryTerm);
         sequentToProve = sequentToProve.addFormula(new SequentFormula(newTerm), false, false).sequent();
         // Compute results and their conditions
         List<Triple<Term, Set<Term>, Node>> conditionsAndResultsMap = computeResultsAndConditions(services, goal, sideProofEnv, sequentToProve, newPredicate);
         // Create new single goal in which the query is replaced by the possible results
         ImmutableList<Goal> goals = goal.split(1);
         Goal resultGoal = goals.head();
         final TermBuilder tb = services.getTermBuilder();
         resultGoal.removeFormula(pio);
         if (pio.isTopLevel() || queryConditionTerm != null) {
            for (Triple<Term, Set<Term>, Node> conditionsAndResult : conditionsAndResultsMap) {
               Term conditionTerm = tb.and(conditionsAndResult.second);
               Term newEqualityTerm = varFirst ? 
                                      tb.equals(varTerm, conditionsAndResult.first) : 
                                      tb.equals(conditionsAndResult.first, varTerm);
               Term resultTerm = pio.isInAntec() ?
                                 tb.imp(conditionTerm, newEqualityTerm) :
                                 tb.and(conditionTerm, newEqualityTerm);
               if (queryConditionTerm != null) {
                  resultTerm = tb.imp(queryConditionTerm, resultTerm);
               }
               resultGoal.addFormula(new SequentFormula(resultTerm), pio.isInAntec(), false);
            }
         }
         else {
            Function resultFunction = createResultConstant(services, varTerm.sort());
            Term resultFunctionTerm = tb.func(resultFunction);
            resultGoal.addFormula(replace(pio, 
                                          varFirst ? tb.equals(resultFunctionTerm, varTerm) : tb.equals(resultFunctionTerm, varTerm),
                                          services), 
                                  pio.isInAntec(), 
                                  false);
            for (Triple<Term, Set<Term>, Node> conditionsAndResult : conditionsAndResultsMap) {
               Term conditionTerm = tb.and(conditionsAndResult.second);
               Term resultTerm = tb.imp(conditionTerm, varFirst ? tb.equals(resultFunctionTerm, conditionsAndResult.first) : tb.equals(conditionsAndResult.first, resultFunctionTerm));
               resultGoal.addFormula(new SequentFormula(resultTerm), true, false);
            }
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