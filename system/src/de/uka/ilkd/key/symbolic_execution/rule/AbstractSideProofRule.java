package de.uka.ilkd.key.symbolic_execution.rule;

import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.IntIterator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;

/**
 * Provides the basic functionality of {@link BuiltInRule} which
 * computes something in a side proof.
 * @author Martin Hentschel
 */
public abstract class AbstractSideProofRule implements BuiltInRule {
   /**
    * <p>
    * Creates a constant which is used in the original {@link Proof} to
    * store the computed result in form of {@code QueryResult = ...}
    * </p>
    * <p>
    * The used name is registered in the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use-
    * @param sort The {@link Sort} to use.
    * @return The created constant.
    */
   protected Function createResultConstant(Services services, Sort sort) {
      String functionName = TermBuilder.DF.newName(services, "QueryResult");
      Function function = new Function(new Name(functionName), sort);
      services.getNamespaces().functions().addSafely(function);
      return function;
   }
   
   /**
    * Creates the result {@link Function} used in a predicate to compute the result in the side proof.
    * @param services The {@link Services} to use.
    * @param sort The {@link Sort} to use.
    * @return The created result {@link Function}.
    */
   protected Function createResultFunction(Services services, Sort sort) {
      return new Function(new Name(TermBuilder.DF.newName(services, "ResultPredicate")), Sort.FORMULA, sort);
   }
   
   /**
    * Computes a general {@link Sequent} to prove in a side proof which
    * contains all {@link SequentFormula} of the original {@link Sequent}
    * except the given current {@link SequentFormula} and those which
    * contains modalities and queries.
    * @param goalSequent The original {@link Sequent} of the current {@link Goal}.
    * @param currentSF The {@link SequentFormula} to ignore.
    * @return The general initial {@link Sequent}.
    */
   protected Sequent computeGeneralSequentToProve(Sequent goalSequent, SequentFormula currentSF) {
      Sequent sequentToProve = Sequent.EMPTY_SEQUENT;
      for (SequentFormula sf : goalSequent.antecedent()) {
         if (sf != currentSF) {
            if (!containsModalityOrQuery(sf)) {
               sequentToProve = sequentToProve.addFormula(sf, true, false).sequent();
            }
         }
      }
      for (SequentFormula sf : goalSequent.succedent()) {
         if (sf != currentSF) {
            if (!containsModalityOrQuery(sf)) {
               sequentToProve = sequentToProve.addFormula(sf, false, false).sequent();
            }
         }
      }
      return sequentToProve;
   }
   
   /**
    * <p>
    * Starts the side proof and extracts the result {@link Term} and conditions.
    * </p>
    * <p>
    * New used names are automatically added to the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use.
    * @param goal The {@link Goal} on which this {@link BuiltInRule} should be applied on.
    * @param sequentToProve The {@link Sequent} to prove in a side proof.
    * @param newPredicate The {@link Function} which is used to compute the result.
    * @return The found result {@link Term} and the conditions.
    * @throws ProofInputException Occurred Exception.
    */
   protected Map<Term, Set<Term>> computeResultsAndConditions(Services services, Goal goal, Sequent sequentToProve, Function newPredicate) throws ProofInputException {
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
      return conditionsAndResultsMap;
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
}
