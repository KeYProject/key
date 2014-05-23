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

import java.util.LinkedHashSet;
import java.util.List;
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
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

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
          // abort if inside of transformer
          if (Transformer.inTransformer(pio)) {
              return false;
          }
          Term term = pio.subTerm();
          term = TermBuilder.goBelowUpdates(term);
          if (term.op() instanceof Modality && SymbolicExecutionUtil.getSymbolicExecutionLabel(term) == null) {
              Term equalityTerm = term.sub(0);
              if (equalityTerm.op() == Junctor.IMP) {
                 equalityTerm = equalityTerm.sub(0);
              }
              if (equalityTerm.op() == Junctor.NOT) {
                 equalityTerm = equalityTerm.sub(0);
              }
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
         Term topLevelTerm = pio.subTerm();
         Pair<ImmutableList<Term>,Term> updatesAndTerm = TermBuilder.goBelowUpdates2(topLevelTerm);
         Term modalityTerm = updatesAndTerm.second;
         ImmutableList<Term> updates = updatesAndTerm.first;
         boolean inImplication = false;
         Term equalityTerm = modalityTerm.sub(0);
         if (equalityTerm.op() == Junctor.IMP) {
            inImplication = true;
            equalityTerm = equalityTerm.sub(0);
         }
         boolean negation = false;
         if (equalityTerm.op() == Junctor.NOT) {
            negation = true;
            equalityTerm = equalityTerm.sub(0);
         }
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
         Sequent sequentToProve = SideProofUtil.computeGeneralSequentToProve(goal.sequent(), pio.constrainedFormula());
         Function newPredicate = createResultFunction(services, varTerm.sort());
         final TermBuilder tb = services.getTermBuilder();
         Term newTerm = tb.func(newPredicate, varTerm);
         Term newModalityTerm = services.getTermFactory().createTerm(modalityTerm.op(), new ImmutableArray<Term>(newTerm), modalityTerm.boundVars(), modalityTerm.javaBlock(), modalityTerm.getLabels());
         Term newModalityWithUpdatesTerm = tb.applySequential(updates, newModalityTerm);
         sequentToProve = sequentToProve.addFormula(new SequentFormula(newModalityWithUpdatesTerm), false, false).sequent();
         // Compute results and their conditions
         List<Triple<Term, Set<Term>, Node>> conditionsAndResultsMap = computeResultsAndConditions(services, goal, sequentToProve, newPredicate);
         // Create new single goal in which the query is replaced by the possible results
         ImmutableList<Goal> goals = goal.split(1);
         Goal resultGoal = goals.head();
         resultGoal.removeFormula(pio);
         // Create results
         Set<Term> resultTerms = new LinkedHashSet<Term>();
         for (Triple<Term, Set<Term>, Node> conditionsAndResult : conditionsAndResultsMap) {
            Term conditionTerm = tb.and(conditionsAndResult.second);
            Term resultEqualityTerm = varFirst ?
                                      tb.equals(conditionsAndResult.first, otherTerm) :
                                      tb.equals(otherTerm, conditionsAndResult.first);
            Term resultTerm = pio.isInAntec() ?
                              tb.imp(conditionTerm, resultEqualityTerm) :
                              tb.and(conditionTerm, resultEqualityTerm);
            resultTerms.add(resultTerm);
         }
         // Add results to goal
         if (inImplication) {
            // Change implication
            Term newCondition = tb.or(resultTerms);
            if (negation) {
               newCondition = tb.not(newCondition);
            }
            Term newImplication = tb.imp(newCondition, modalityTerm.sub(0).sub(1));
            Term newImplicationWithUpdates = tb.applySequential(updates, newImplication);
            resultGoal.addFormula(new SequentFormula(newImplicationWithUpdates), pio.isInAntec(), false);
         }
         else {
            // Add result directly as new top level formula
            for (Term result : resultTerms) {
               resultGoal.addFormula(new SequentFormula(result), pio.isInAntec(), false);
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