package de.uka.ilkd.key.symbolic_execution.rule;

import java.security.KeyStore.Builder;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.DefaultBuiltInRuleApp;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * <p>
 * A {@link Builder} which evaluates a query in a side proof.
 * </p>
 * <p>
 * This rule is only applicable on top level formulas of the form 
 * {@code <var> = <query>},
 * {@code <query> = <var>},
 * {@code <pre> -> <var> = <query>} or
 * {@code <pre> -> <query> = <var>}.
 * </p>
 * <p>
 * In the following Goal the equality term is removed and for each possible
 * result is a new top level formula of the form 
 * {@code <resultCondition> -> <var> = <result>}, 
 * {@code <resultCondition> -> <result> = <var>},
 * {@code <pre> -> <resultCondition> -> <var> = <result>} or 
 * {@code <pre> -> <resultCondition> -> <result> = <var>} 
 * added. The side proof uses the default side proof settings (splitting = delayed) and is started
 * via {@link SymbolicExecutionUtil#startSideProof(de.uka.ilkd.key.proof.Proof, Sequent, String)}.
 * In case that at least one result branch has applicable rules an exception is thrown and the rule is aborted.
 * </p>
 * @author Martin Hentschel
 */
public final class QuerySideProofRule implements BuiltInRule {
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
         Term term = null;
         if (pio.isTopLevel()) {
            term = pio.subTerm();
         }
         else {
            Term topTerm = pio.constrainedFormula().formula();
            if (topTerm.op() == Junctor.IMP) {
               if (topTerm.sub(1) == pio.subTerm()) {
                  term = pio.subTerm();
               }
            }
         }
         if (term != null) {
            if (term.op() == Equality.EQUALS) {
               if (term.sub(0).op() instanceof LocationVariable) {
                  applicable = isApplicableQuery(goal, term.sub(1), pio);
               }
               else if (term.sub(1).op() instanceof LocationVariable) {
                  applicable = isApplicableQuery(goal, term.sub(0), pio);
               }
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
         Sequent goalSequent = goal.sequent();
         SequentFormula equalitySF = ruleApp.posInOccurrence().constrainedFormula();
         Term equalityTerm = ruleApp.posInOccurrence().subTerm();
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
         if (equalitySF.formula().op() == Junctor.IMP) {
            queryConditionTerm = equalitySF.formula().sub(0); 
         }
         // Compute sequent for side proof to compute query in.
         Sequent sequentToProve = Sequent.EMPTY_SEQUENT;
         for (SequentFormula sf : goalSequent.antecedent()) {
            if (sf != equalitySF) {
               if (!containsModalityOrQuery(sf)) {
                  sequentToProve = sequentToProve.addFormula(sf, true, false).sequent();
               }
            }
         }
         for (SequentFormula sf : goalSequent.succedent()) {
            if (sf != equalitySF) {
               if (!containsModalityOrQuery(sf)) {
                  sequentToProve = sequentToProve.addFormula(sf, false, false).sequent();
               }
            }
         }
         if (queryConditionTerm != null) {
            // Add query condition to antecedent because it reduces the number of required steps to prove the result
            sequentToProve = sequentToProve.addFormula(new SequentFormula(queryConditionTerm), true, false).sequent();
         }
         Function newPredicate = new Function(new Name(TermBuilder.DF.newName(services, "ResultPredicate")), Sort.FORMULA, queryTerm.sort());
         Term newTerm = TermBuilder.DF.func(newPredicate, queryTerm);
         sequentToProve = sequentToProve.addFormula(new SequentFormula(newTerm), false, false).sequent();
         // Execute side proof
         ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(goal.proof(), sequentToProve, StrategyProperties.SPLITTING_DELAYED);
         // Extract relevant things
         Set<Operator> relevantThingsInSequentToProve = extractRelevantThings(info.getProof().getServices(), sequentToProve);
         // Extract results and conditions from side proof
         Map<Term, Set<Term>> conditionsAndResultsMap = new LinkedHashMap<Term, Set<Term>>();
         for (Goal resultGoal : info.getProof().openGoals()) {
            if (resultGoal.getRuleAppManager().peekNext() != null) {
               throw new IllegalStateException("Side roof contains goal with automatic applicable rules.");
            }
            Sequent sequent = resultGoal.sequent();

            Term condition = TermBuilder.DF.tt();
            Term result = null;
            for (SequentFormula sf : sequent.antecedent()) {
               if (sf.formula().op() == newPredicate) {
                  throw new IllegalStateException("Result predicate found in antecedent.");
               }
               if (!isIrrelevantCondition(services, sequentToProve, relevantThingsInSequentToProve, sf)) {
                  condition = TermBuilder.DF.and(condition, sf.formula());
               }
            }
            for (SequentFormula sf : sequent.succedent()) {
               if (sf.formula().op() == newPredicate) {
                  if (result != null) {
                     throw new IllegalStateException("Result predicate found multiple times in succedent.");
                  }
                  result = sf.formula().sub(0);
               }
               else {
                  if (!isIrrelevantCondition(services, sequentToProve, relevantThingsInSequentToProve, sf)) {
                     condition = TermBuilder.DF.and(condition, TermBuilder.DF.not(sf.formula()));
                  }
               }
            }
            Set<Term> conditions = conditionsAndResultsMap.get(result);
            if (conditions == null) {
               conditions = new LinkedHashSet<Term>();
               conditionsAndResultsMap.put(result, conditions);
            }
            conditions.add(condition);
         }
         // Create new single goal in which the query is replaced by the possible results
         ImmutableList<Goal> goals = goal.split(1);
         Goal resultGoal = goals.head();
         resultGoal.removeFormula(ruleApp.posInOccurrence());
         for (Entry<Term, Set<Term>> conditionsAndResult : conditionsAndResultsMap.entrySet()) {
            Term resultTerm = TermBuilder.DF.imp(TermBuilder.DF.or(conditionsAndResult.getValue()), 
                                                 varFirst ? TermBuilder.DF.equals(varTerm, conditionsAndResult.getKey()) : TermBuilder.DF.equals(conditionsAndResult.getKey(), varTerm));
            if (queryConditionTerm != null) {
               resultTerm = TermBuilder.DF.imp(queryConditionTerm, resultTerm);
            }
            resultGoal.addFormula(new SequentFormula(resultTerm), true, false);
         }
         return goals;
      }
      catch (Exception e) {
         throw new RuleAbortException(e.getMessage());
      }
   }

   /**
    * Extracts all {@link Operator}s from the given {@link Sequent} which
    * represents relevant things.
    * @param services The {@link Services} to use.
    * @param sequentToProve The {@link Sequent} to extract relevant things from.
    * @return The found relevant things.
    */
   private Set<Operator> extractRelevantThings(final Services services, 
                                               Sequent sequentToProve) {
      final Set<Operator> result = new HashSet<Operator>();
      for (SequentFormula sf : sequentToProve) {
         sf.formula().execPreOrder(new DefaultVisitor() {
            @Override
            public void visit(Term visited) {
               if (isRelevantThing(services, visited)) {
                  result.add(visited.op());
               }
            }
         });
      }
      return result;
   }
   
   /**
    * Checks if the given {@link Term} describes a relevant thing. 
    * Relevant things are:
    * <ul>
    *    <li>IProgramVariable</li>
    *    <li>Functions of type Heap</li>
    *    <li>Functions of a Java type</li>
    * </ul>
    * @param services The {@link Services} to use.
    * @param term The {@link Term} to check.
    * @return {@code true} is relevant thing, {@code false} is not relevant.
    */
   protected static boolean isRelevantThing(Services services, Term term) {
      if (term.op() instanceof IProgramVariable) {
         return true;
      }
      else if (term.op() instanceof Function) {
         HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
         if (SymbolicExecutionUtil.isHeap(term.op(), heapLDT)) {
            return true;
         }
         else {
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(term.sort());
            return kjt != null;
         }
      }
      else {
         return false;
      }
   }

   /**
    * Checks if the given {@link SequentFormula} is a relevant condition.
    * @param services The {@link Services} to use.
    * @param initialSequent The initial {@link Sequent} of the side proof.
    * @param relevantThingsInSequentToProve The relevant things found in the initial {@link Sequent}.
    * @param sf The {@link SequentFormula} to check.
    * @return {@code true} {@link SequentFormula} is relevant condition, {@code false} {@link SequentFormula} is not a relevant condition.
    */
   protected boolean isIrrelevantCondition(Services services, 
                                           Sequent initialSequent, 
                                           Set<Operator> relevantThingsInSequentToProve, 
                                           SequentFormula sf) {
      return initialSequent.antecedent().contains(sf) || // Conditions which already exist in the initial sequent are irrelevant
             initialSequent.succedent().contains(sf) || // Conditions which already exist in the initial sequent are irrelevant
             containsModalityOrQuery(sf) || // Conditions with modalities or queries are irrelevant
             containsIrrelevantThings(services, sf, relevantThingsInSequentToProve); // Conditions which contains not relevant things are irrelevant
   }

   /**
    * Checks if the given {@link SequentFormula} contains irrelevant things
    * (things which are not contained in the relevantThingsToProve and are no Java types)
    * @param services The {@link Services} to use.
    * @param sf The {@link SequentFormula} to check.
    * @param relevantThings The relevant things.
    * @return {@code true} The {@link SequentFormula} contains irrelevant things, {@code false} the {@link SequentFormula} contains no irrelevant things.
    */
   protected boolean containsIrrelevantThings(Services services,
                                              SequentFormula sf,
                                              Set<Operator> relevantThings) {
      ContainsIrrelevantThingsVisitor visitor = new ContainsIrrelevantThingsVisitor(services, relevantThings);
      sf.formula().execPostOrder(visitor);
      return visitor.isContainsIrrelevantThings();
   }
   
   /**
    * Utility class used by {@link QuerySideProofRule#containsIrrelevantThings(Services, SequentFormula, Set)}.
    * @author Martin Hentschel
    */
   protected static class ContainsIrrelevantThingsVisitor extends DefaultVisitor {
      /**
       * The {@link Services} to use.
       */
      private Services services;
      
      /**
       * The relevant things.
       */
      private Set<Operator> relevantThings;
      
      /**
       * The result.
       */
      boolean containsIrrelevantThings = false;
      
      /**
       * Constructor.
       * @param services The {@link Services} to use.
       * @param relevantThings The relevant things.
       */
      public ContainsIrrelevantThingsVisitor(Services services, Set<Operator> relevantThings) {
         this.services = services;
         this.relevantThings = relevantThings;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Term visited) {
         if (isRelevantThing(services, visited)) {
            if (!SymbolicExecutionUtil.isSelect(services, visited) &&
                !SymbolicExecutionUtil.isBoolean(services, visited.op()) &&
                !SymbolicExecutionUtil.isNumber(visited.op())) {
               if (!relevantThings.contains(visited.op())) {
                  containsIrrelevantThings = true;
               }
            }
         }
      }

      /**
       * Returns the result.
       * @return The {@link SequentFormula} contains irrelevant things, {@code false} the {@link SequentFormula} contains no irrelevant things.
       */
      public boolean isContainsIrrelevantThings() {
         return containsIrrelevantThings;
      }
   }

   /**
    * Checks if the given {@link SequentFormula} contains a modality or query.
    * @param sf The {@link SequentFormula} to check.
    * @return {@code true} contains at least one modality or query, {@code false} contains no modalities and no queries.
    */
   protected boolean containsModalityOrQuery(SequentFormula sf) {
      return containsModalityOrQuery(sf.formula());
   }

   /**
    * Checks if the given {@link Term} contains a modality or query.
    * @param term The {@link Term} to check.
    * @return {@code true} contains at least one modality or query, {@code false} contains no modalities and no queries.
    */
   protected boolean containsModalityOrQuery(Term term) {
      ContainsModalityOrQueryVisitor visitor = new ContainsModalityOrQueryVisitor();
      term.execPostOrder(visitor);
      return visitor.isContainsModalityOrQuery();
   }
   
   /**
    * Utility method used by {@link QuerySideProofRule#containsModalityOrQuery(Term)}.
    * @author Martin Hentschel
    */
   protected static class ContainsModalityOrQueryVisitor extends DefaultVisitor {
      /**
       * The result.
       */
      boolean containsModalityOrQuery = false;

      /**
       * {@inheritDoc}
       */
      @Override
      public void visit(Term visited) {
         if (visited.op() instanceof Modality) {
            containsModalityOrQuery = true;
         }
         else if (visited.op() instanceof IProgramMethod) {
            containsModalityOrQuery = true;
         }
      }

      /**
       * Returns the result.
       * @return {@code true} contains at least one modality or query, {@code false} contains no modalities and no queries.
       */
      public boolean isContainsModalityOrQuery() {
         return containsModalityOrQuery;
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
