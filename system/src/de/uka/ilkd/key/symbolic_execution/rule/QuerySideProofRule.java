package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
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
import de.uka.ilkd.key.util.Pair;

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
 *          <li>Antecedent: {@code <resultCondition> -> <result> = <something>}</li>
 *          <li>Succedent: {@code <resultCondition> & <something> = <result>} or </li>
 *          <li>Succedent: {@code <resultCondition> & <result> = <something>}</li>
 *       </ul>
 *    </li>
 *    <li>
 *       <b>right side of an implication on top level {@code <queryCondition> -> <something> = <query>} or {@code <queryCondition> -> <query> = <something>}</b><br>
 *       For each possible result value is a {@link SequentFormula} added to the {@link Sequent} of the form:
 *       <ul>
 *          <li>Antecedent: {@code <pre> -> (<resultCondition> -> <something> = <result>)} or </li>
 *          <li>Antecedent: {@code <pre> -> (<resultCondition> -> <result> = <something>)}</li>
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
            Set<Term> resultConditions = new LinkedHashSet<Term>();
            Term result = null;
            for (SequentFormula sf : sequent.antecedent()) {
               if (sf.formula().op() == newPredicate) {
                  throw new IllegalStateException("Result predicate found in antecedent.");
               }
               if (!isIrrelevantCondition(services, sequentToProve, relevantThingsInSequentToProve, sf)) {
                  if (resultConditions.add(sf.formula())) {
                     addNewNamesToNamespace(services, sf.formula());
                  }
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
                     if (resultConditions.add(TermBuilder.DF.not(sf.formula()))) {
                        addNewNamesToNamespace(services, sf.formula());
                     }
                  }
               }
            }
            Set<Term> conditions = conditionsAndResultsMap.get(result);
            if (conditions == null) {
               conditions = new LinkedHashSet<Term>();
               conditionsAndResultsMap.put(result, conditions);
            }
            conditions.add(TermBuilder.DF.and(resultConditions));
         }
         // Create new single goal in which the query is replaced by the possible results
         ImmutableList<Goal> goals = goal.split(1);
         Goal resultGoal = goals.head();
         resultGoal.removeFormula(pio);
         if (pio.isTopLevel() || queryConditionTerm != null) {
            for (Entry<Term, Set<Term>> conditionsAndResult : conditionsAndResultsMap.entrySet()) {
               for (Term conditionTerm : conditionsAndResult.getValue()) { // Combining the different conditions for the same value with an OR does not work well because the strategy then tries to establish CNF by splitting or ausmultiplizieren
                  Term newEqualityTerm = varFirst ? 
                                         TermBuilder.DF.equals(varTerm, conditionsAndResult.getKey()) : 
                                         TermBuilder.DF.equals(conditionsAndResult.getKey(), varTerm);
                  Term resultTerm = pio.isInAntec() ?
                                    TermBuilder.DF.imp(conditionTerm, newEqualityTerm) :
                                    TermBuilder.DF.and(conditionTerm, newEqualityTerm);
                  if (queryConditionTerm != null) {
                     resultTerm = TermBuilder.DF.imp(queryConditionTerm, resultTerm);
                  }
                  resultGoal.addFormula(new SequentFormula(resultTerm), pio.isInAntec(), false);
               }
            }
         }
         else {
            String functionName = TermBuilder.DF.newName(services, "QueryResult");
            Function resultFunction = new Function(new Name(functionName), varTerm.sort());
            services.getNamespaces().functions().addSafely(resultFunction);
            Term resultFunctionTerm = TermBuilder.DF.func(resultFunction);
            resultGoal.addFormula(replace(pio, varFirst ? TermBuilder.DF.equals(resultFunctionTerm, varTerm) : TermBuilder.DF.equals(resultFunctionTerm, varTerm)), pio.isInAntec(), false);
            for (Entry<Term, Set<Term>> conditionsAndResult : conditionsAndResultsMap.entrySet()) {
               for (Term conditionTerm : conditionsAndResult.getValue()) { // Combining the different conditions for the same value with an OR does not work well because the strategy then tries to establish CNF by splitting or ausmultiplizieren
                  Term resultTerm = TermBuilder.DF.imp(conditionTerm, varFirst ? TermBuilder.DF.equals(resultFunctionTerm, conditionsAndResult.getKey()) : TermBuilder.DF.equals(conditionsAndResult.getKey(), resultFunctionTerm));
                  resultGoal.addFormula(new SequentFormula(resultTerm), true, false);
               }
            }
         }
         return goals;
      }
      catch (Exception e) {
         throw new RuleAbortException(e.getMessage());
      }
   }
   
   /**
    * Makes sure that all used {@link Name}s in the given {@link Term}
    * are registered in the {@link Namespace}s of the given {@link Services}.
    * @param services The {@link Services} to use.
    * @param term The {@link Term} to check its {@link Name}s.
    */
   protected void addNewNamesToNamespace(Services services, Term term) {
      final Namespace functions = services.getNamespaces().functions();
      final Namespace progVars = services.getNamespaces().programVariables();
      // LogicVariables are always local bound
      term.execPreOrder(new DefaultVisitor() {
         @Override
         public void visit(Term visited) {
            if (visited.op() instanceof Function) {
               functions.add((Function)visited.op());
            }
            else if (visited.op() instanceof IProgramVariable) {
               progVars.add((IProgramVariable)visited.op());
            }
         }
      });
   }

   /**
    * Extracts all {@link Operator}s from the given {@link Sequent} which
    * represents relevant things.
    * @param services The {@link Services} to use.
    * @param sequentToProve The {@link Sequent} to extract relevant things from.
    * @return The found relevant things.
    */
   protected Set<Operator> extractRelevantThings(final Services services, 
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
    * Replaces the {@link Term} defined by the given {@link PosInOccurrence}
    * with the given new {@link Term}.
    * @param pio The {@link PosInOccurrence} which defines the {@link Term} to replace.
    * @param newTerm The new {@link Term}.
    * @return The created {@link SequentFormula} in which the {@link Term} is replaced.
    */
   protected static SequentFormula replace(PosInOccurrence pio, Term newTerm) {
      // Iterate along the PosInOccurrence and collect the parents and indices
      Deque<Pair<Integer, Term>> indexAndParents = new LinkedList<Pair<Integer, Term>>();
      Term root = pio.constrainedFormula().formula();
      IntIterator iter = pio.posInTerm().iterator();
      while (iter.hasNext()) {
         int next = iter.next();
         indexAndParents.addFirst(new Pair<Integer, Term>(Integer.valueOf(next), root));
         root = root.sub(next);
      }
      // Iterate over the collected parents and replace terms
      root = newTerm;
      for (Pair<Integer, Term> pair : indexAndParents) {
         Term parent = pair.second;
         Term[] newSubs = parent.subs().toArray(new Term[parent.subs().size()]);
         newSubs[pair.first] = root;
         root = TermFactory.DEFAULT.createTerm(parent.op(), newSubs, parent.boundVars(), parent.javaBlock(), parent.getLabels());
      }
      return new SequentFormula(root);
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
