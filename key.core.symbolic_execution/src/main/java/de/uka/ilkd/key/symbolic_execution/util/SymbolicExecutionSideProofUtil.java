package de.uka.ilkd.key.symbolic_execution.util;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager.TermLabelConfiguration;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationInfo;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.profile.SimplifyTermProfile;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.rule.QuerySideProofRule;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import de.uka.ilkd.key.util.Triple;

/**
 * Provides utility methods for side proofs.
 * @author Martin Hentschel
 */
public final class SymbolicExecutionSideProofUtil {
   /**
    * Forbid instances.
    */
   private SymbolicExecutionSideProofUtil() {
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
   public static Sequent computeGeneralSequentToProve(Sequent goalSequent, SequentFormula currentSF) {
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
    * Starts the side proof and extracts the result {@link Term}.
    * </p>
    * <p>
    * New used names are automatically added to the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use.
    * @param proof The {@link Proof} from on which the side proof si performed.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to prove in a side proof.
    * @param label The {@link TermLabel} which is used to compute the result.
    * @param description The side proof description.
    * @param splittingOption The splitting options to use.
    * @param addNamesToServices {@code true} defines that used names in result and conditions are added to the namespace of the given {@link Services}, {@code false} means that names are not added.
    * @return The found result {@link Term} and the conditions.
    * @throws ProofInputException Occurred Exception.
    */
   public static List<Pair<Term, Node>> computeResults(Services services, 
                                                       Proof proof, 
                                                       ProofEnvironment sideProofEnvironment,
                                                       Sequent sequentToProve, 
                                                       TermLabel label, 
                                                       String description,
                                                       String methodTreatment,
                                                       String loopTreatment,
                                                       String queryTreatment,
                                                       String splittingOption,
                                                       boolean addNamesToServices) throws ProofInputException {
      // Execute side proof
      ApplyStrategyInfo info = startSideProof(proof, sideProofEnvironment, sequentToProve, methodTreatment, loopTreatment, queryTreatment, splittingOption);
      try {
         // Extract results and conditions from side proof
         List<Pair<Term, Node>> conditionsAndResultsMap = new LinkedList<Pair<Term, Node>>();
         for (Goal resultGoal : info.getProof().openGoals()) {
            if (SymbolicExecutionUtil.hasApplicableRules(resultGoal)) {
               throw new IllegalStateException("Not all applicable rules are applied.");
            }
            Sequent sequent = resultGoal.sequent();
            List<Term> results = new LinkedList<Term>();
            for (SequentFormula sf : sequent.antecedent()) {
               if (sf.formula().containsLabel(label)) {
                  Term result = sf.formula();
                  result = services.getTermBuilder().not(result);
                  results.add(result);
               }
            }
            for (SequentFormula sf : sequent.succedent()) {
               if (sf.formula().containsLabel(label)) {
                  Term result = sf.formula();
                  results.add(result);
               }
            }
            Term result;
            if (results.isEmpty()) {
               result = services.getTermBuilder().tt();
            }
            else {
               result = services.getTermBuilder().or(results);
            }
            conditionsAndResultsMap.add(new Pair<Term, Node>(result, resultGoal.node()));
         }
         return conditionsAndResultsMap;
      }
      finally {
         disposeOrStore(description, info);
      }
   }
   
   /**
    * <p>
    * Starts the side proof and extracts the result {@link Term} and conditions.
    * </p>
    * <p>
    * New used names are automatically added to the {@link Namespace} of the {@link Services}.
    * </p>
    * @param services The {@link Services} to use.
    * @param proof The {@link Proof} from on which the side proof si performed.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to prove in a side proof.
    * @param operator The {@link Operator} which is used to compute the result.
    * @param description The side proof description.
    * @param splittingOption The splitting options to use.
    * @param addNamesToServices {@code true} defines that used names in result and conditions are added to the namespace of the given {@link Services}, {@code false} means that names are not added.
    * @return The found result {@link Term} and the conditions.
    * @throws ProofInputException Occurred Exception.
    */
   public static List<Triple<Term, Set<Term>, Node>> computeResultsAndConditions(Services services, 
                                                                                 Proof proof, 
                                                                                 ProofEnvironment sideProofEnvironment, 
                                                                                 Sequent sequentToProve, 
                                                                                 Operator operator, 
                                                                                 String description,
                                                                                 String methodTreatment,
                                                                                 String loopTreatment,
                                                                                 String queryTreatment,
                                                                                 String splittingOption,
                                                                                 boolean addNamesToServices) throws ProofInputException {
      // Execute side proof
      ApplyStrategyInfo info = startSideProof(proof, sideProofEnvironment, sequentToProve, methodTreatment, loopTreatment, queryTreatment, splittingOption);
      try {
         // Extract relevant things
         Set<Operator> relevantThingsInSequentToProve = extractRelevantThings(info.getProof().getServices(), sequentToProve);
         // Extract results and conditions from side proof
         List<Triple<Term, Set<Term>, Node>> conditionsAndResultsMap = new LinkedList<Triple<Term, Set<Term>, Node>>();
         for (Goal resultGoal : info.getProof().openGoals()) {
            if (SymbolicExecutionUtil.hasApplicableRules(resultGoal)) {
               throw new IllegalStateException("Not all applicable rules are applied.");
            }
            Sequent sequent = resultGoal.sequent();
            boolean newPredicateIsSequentFormula = isOperatorASequentFormula(sequent, operator);
            Set<Term> resultConditions = new LinkedHashSet<Term>();
            Term result = null;
            for (SequentFormula sf : sequent.antecedent()) {
               if (newPredicateIsSequentFormula) {
                  if (sf.formula().op() == operator) {
                     throw new IllegalStateException("Result predicate found in antecedent.");
                  }
                  else {
                     Term constructedResult = constructResultIfContained(services, sf, operator);
                     if (constructedResult != null) {
                        throw new IllegalStateException("Result predicate found in antecedent.");
                     }
                  }
               }
               if (!isIrrelevantCondition(services, sequentToProve, relevantThingsInSequentToProve, sf)) {
                  if (resultConditions.add(sf.formula()) && addNamesToServices) {
                     addNewNamesToNamespace(services, sf.formula());
                  }
               }
            }
            for (SequentFormula sf : sequent.succedent()) {
               if (newPredicateIsSequentFormula) {
                  if (sf.formula().op() == operator) {
                     if (result != null) {
                        throw new IllegalStateException("Result predicate found multiple times in succedent.");
                     }
                     result = sf.formula().sub(0);
                  }
               }
               else {
                  Term constructedResult = constructResultIfContained(services, sf, operator);
                  if (constructedResult != null) {
                     if (result != null) {
                        throw new IllegalStateException("Result predicate found multiple times in succedent.");
                     }
                     result = constructedResult;
                  }
               }
               if (result == null) {
                  if (!isIrrelevantCondition(services, sequentToProve, relevantThingsInSequentToProve, sf)) {
                     if (resultConditions.add(services.getTermBuilder().not(sf.formula())) && addNamesToServices) {
                        addNewNamesToNamespace(services, sf.formula());
                     }
                  }
               }
            }
            if (result == null) {
               result = services.getTermBuilder().ff();
            }
            conditionsAndResultsMap.add(new Triple<Term, Set<Term>, Node>(result, resultConditions, resultGoal.node()));
         }
         return conditionsAndResultsMap;
      }
      finally {
         disposeOrStore(description, info);
      }
   }
   
   private static Term constructResultIfContained(Services services, SequentFormula sf, Operator operator) {
      return constructResultIfContained(services, sf.formula(), operator);
   }
   
   private static Term constructResultIfContained(Services services, Term term, Operator operator) {
      if (term.op() == operator) {
         return term.sub(0);
      }
      else {
         Term result = null;
         int i = 0;
         while (result == null && i < term.arity()) {
            result = constructResultIfContained(services, term.sub(i), operator);
            i++;
         }
         if (result != null) {
            List<Term> newSubs = new LinkedList<Term>();
            for (int j = 0; j < term.arity(); j++) {
               if (j == i - 1) {
                  newSubs.add(result);
               }
               else {
                  newSubs.add(term.sub(j));
               }
            }
            result = services.getTermFactory().createTerm(term.op(), new ImmutableArray<Term>(newSubs), term.boundVars(), term.javaBlock(), term.getLabels());
         }
         return result;
      }
   }

   private static boolean isOperatorASequentFormula(Sequent sequent, final Operator operator) {
      return CollectionUtil.search(sequent, new IFilter<SequentFormula>() {
         @Override
         public boolean select(SequentFormula element) {
            return element.formula().op() == operator;
         }
      }) != null;
   }

   /**
    * Makes sure that all used {@link Name}s in the given {@link Term}
    * are registered in the {@link Namespace}s of the given {@link Services}.
    * @param services The {@link Services} to use.
    * @param term The {@link Term} to check its {@link Name}s.
    */
   public static void addNewNamesToNamespace(Services services, Term term) {
      final Namespace<Function> functions = services.getNamespaces().functions();
      final Namespace<IProgramVariable> progVars = services.getNamespaces().programVariables();
      // LogicVariables are always local bound
      term.execPreOrder(new DefaultVisitor() {
         @Override
         public void visit(Term visited) {
            if (visited.op() instanceof Function) {
               functions.add((Function) visited.op());
            }
            else if (visited.op() instanceof IProgramVariable) {
               progVars.add((IProgramVariable) visited.op());
            }
         }
      });
   }
   
   /**
    * Checks if the given {@link SequentFormula} contains a modality or query.
    * @param sf The {@link SequentFormula} to check.
    * @return {@code true} contains at least one modality or query, {@code false} contains no modalities and no queries.
    */
   public static boolean containsModalityOrQuery(SequentFormula sf) {
      return containsModalityOrQuery(sf.formula());
   }

   /**
    * Checks if the given {@link Term} contains a modality or query.
    * @param term The {@link Term} to check.
    * @return {@code true} contains at least one modality or query, {@code false} contains no modalities and no queries.
    */
   public static boolean containsModalityOrQuery(Term term) {
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
    * Extracts all {@link Operator}s from the given {@link Sequent} which
    * represents relevant things.
    * @param services The {@link Services} to use.
    * @param sequentToProve The {@link Sequent} to extract relevant things from.
    * @return The found relevant things.
    */
   public static Set<Operator> extractRelevantThings(final Services services, 
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
   public static boolean isIrrelevantCondition(Services services, 
                                               Sequent initialSequent, 
                                               Set<Operator> relevantThingsInSequentToProve, 
                                               SequentFormula sf) {
      return initialSequent.antecedent().contains(sf) || // Conditions which already exist in the initial sequent are irrelevant
             initialSequent.succedent().contains(sf) || // Conditions which already exist in the initial sequent are irrelevant
//             isInOrOfAntecedent(initialSequent, sf) ||
             containsModalityOrQuery(sf) || // Conditions with modalities or queries are irrelevant
             containsIrrelevantThings(services, sf, relevantThingsInSequentToProve); // Conditions which contains not relevant things are irrelevant
   }

//   public static boolean isInOrOfAntecedent(Sequent initialSequent, SequentFormula sf) {
//      Term term = sf.formula();
//      boolean result = false;
//      Iterator<SequentFormula> iter = initialSequent.antecedent().iterator();
//      while (!result && iter.hasNext()) {
//         SequentFormula next = iter.next();
//         if (isInOr(next.formula(), term)) {
//            result = true;
//         }
//      }
//      return result;
//   }
//
//   public static boolean isInOr(Term term, Term toCheck) {
//      if (term.op() == Junctor.OR) {
//         boolean result = false;
//         Iterator<Term> iter = term.subs().iterator();
//         while (!result && iter.hasNext()) {
//            result = isInOr(iter.next(), toCheck);
//         }
//         return result;
//      }
//      else {
//         return term == toCheck;
//      }
//   }

   /**
    * Checks if the given {@link SequentFormula} contains irrelevant things
    * (things which are not contained in the relevantThingsToProve and are no Java types)
    * @param services The {@link Services} to use.
    * @param sf The {@link SequentFormula} to check.
    * @param relevantThings The relevant things.
    * @return {@code true} The {@link SequentFormula} contains irrelevant things, {@code false} the {@link SequentFormula} contains no irrelevant things.
    */
   public static boolean containsIrrelevantThings(Services services,
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
    * Starts a site proof for the given {@link Sequent}.
    * @param proof The parent {@link Proof} of the site proof to do.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to prove.
    * @return The proof result represented as {@link ApplyStrategyInfo} instance.
    * @throws ProofInputException Occurred Exception
    */
   public static ApplyStrategyInfo startSideProof(Proof proof,
                                                  ProofEnvironment sideProofEnvironment,
                                                  Sequent sequentToProve) throws ProofInputException {
      return startSideProof(proof, 
                            sideProofEnvironment,
                            sequentToProve, 
                            StrategyProperties.METHOD_NONE,
                            StrategyProperties.LOOP_NONE,
                            StrategyProperties.QUERY_OFF,
                            StrategyProperties.SPLITTING_OFF);
   }
   
   /**
    * Starts a site proof for the given {@link Sequent}.
    * @param proof The parent {@link Proof} of the site proof to do.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to prove.
    * @return The proof result represented as {@link ApplyStrategyInfo} instance.
    * @throws ProofInputException Occurred Exception
    */
   public static ApplyStrategyInfo startSideProof(Proof proof,
                                                  ProofEnvironment sideProofEnvironment,
                                                  Sequent sequentToProve,
                                                  String methodTreatment,
                                                  String loopTreatment,
                                                  String queryTreatment,
                                                  String splittingOption) throws ProofInputException {
      ProofStarter starter = createSideProof(sideProofEnvironment, sequentToProve, null);
      return startSideProof(proof, starter, methodTreatment, loopTreatment, queryTreatment, splittingOption);
   }
   
   /**
    * Creates a new {@link ProofStarter} which contains a new site proof
    * of the given {@link Proof}.
    * @param sideProofEnvironment The given {@link ProofEnvironment} of the side proof.
    * @param sequentToProve The {@link Sequent} to proof in a new site proof.
    * @param proofName An optional name for the newly created {@link Proof}.
    * @return The created {@link ProofStarter} with the site proof.
    * @throws ProofInputException Occurred Exception.
    */
   public static ProofStarter createSideProof(ProofEnvironment sideProofEnvironment,
                                              Sequent sequentToProve,
                                              String proofName) throws ProofInputException {
      return SideProofUtil.createSideProof(sideProofEnvironment, sequentToProve, proofName);
   }
   
   /**
    * Starts a site proof.
    * @param proof The original {@link Proof}.
    * @param starter The {@link ProofStarter} with the site proof.
    * @param splittingOption The splitting option to use.
    * @return The site proof result.
    */
   public static ApplyStrategyInfo startSideProof(Proof proof, 
                                                  ProofStarter starter,
                                                  String methodTreatment,
                                                  String loopTreatment,
                                                  String queryTreatment,
                                                  String splittingOption) {
      assert starter != null;
      starter.setMaxRuleApplications(10000);
      StrategyProperties sp = proof != null && !proof.isDisposed() ? 
                              proof.getSettings().getStrategySettings().getActiveStrategyProperties() : // Is a clone that can be modified
                              new StrategyProperties();
      StrategyProperties.setDefaultStrategyProperties(sp, false, true, true, false, false, false);
      sp.setProperty(StrategyProperties.METHOD_OPTIONS_KEY, methodTreatment);
      sp.setProperty(StrategyProperties.LOOP_OPTIONS_KEY, loopTreatment);
      sp.setProperty(StrategyProperties.QUERY_OPTIONS_KEY, queryTreatment);
      sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, splittingOption);
      sp.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, StrategyProperties.QUANTIFIERS_NON_SPLITTING);
      starter.setStrategyProperties(sp);
      // Execute proof in the current thread
      return starter.start();
   }

   /**
    * Extracts the value for the formula with the given {@link Operator}
    * from the given {@link Goal}.
    * @param goal The {@link Goal} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The value of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorValue(Goal goal, final Operator operator) {
      assert goal != null;
      return extractOperatorValue(goal.node(), operator);
   }

   /**
    * Extracts the value for the formula with the given {@link Operator}
    * from the given {@link Node}.
    * @param node The {@link Node} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The value of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorValue(Node node, final Operator operator) {
      Term operatorTerm = extractOperatorTerm(node, operator);
      return operatorTerm != null ? operatorTerm.sub(0) : null;
   }
   
   /**
    * Extracts the operator term for the formula with the given {@link Operator}
    * from the site proof result ({@link ApplyStrategyInfo}).
    * @param info The site proof result.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The operator term of the formula with the given {@link Operator}.
    * @throws ProofInputException Occurred Exception.
    */
   public static Term extractOperatorTerm(ApplyStrategyInfo info, Operator operator) throws ProofInputException {
      // Make sure that valid parameters are given
      assert info != null;
      if (info.getProof().openGoals().size() != 1) {
         throw new ProofInputException("Assumption that return value extraction has one goal does not hold because " + info.getProof().openGoals().size() + " goals are available.");
      }
      // Get node of open goal
      return extractOperatorTerm(info.getProof().openGoals().head(), operator);
   }

   /**
    * Extracts the operator term for the formula with the given {@link Operator}
    * from the given {@link Goal}.
    * @param goal The {@link Goal} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The operator term of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorTerm(Goal goal, final Operator operator) {
      assert goal != null;
      return extractOperatorTerm(goal.node(), operator);
   }

   /**
    * Extracts the operator term for the formula with the given {@link Operator}
    * from the given {@link Node}.
    * @param node The {@link Node} to search the {@link Operator} in.
    * @param operator The {@link Operator} for the formula which should be extracted.
    * @return The operator term of the formula with the given {@link Operator}.
    */
   public static Term extractOperatorTerm(Node node, final Operator operator) {
      assert node != null;
      // Search formula with the given operator in sequent (or in some cases below the updates)
      SequentFormula sf = CollectionUtil.search(node.sequent(), new IFilter<SequentFormula>() {
         @Override
         public boolean select(SequentFormula element) {
            Term term = element.formula();
            term = TermBuilder.goBelowUpdates(term);
            return ObjectUtil.equals(term.op(), operator);
         }
      });
      if (sf != null) {
         Term term = sf.formula();
         term = TermBuilder.goBelowUpdates(term);
         return term;
      }
      else {
         return null;
      }
   }
   
   /**
    * Creates a copy of the {@link ProofEnvironment} of the given {@link Proof}
    * which has his own {@link OneStepSimplifier} instance. Such copies are
    * required for instance during parallel usage of site proofs because
    * {@link OneStepSimplifier} has an internal state.
    * @param source The {@link Proof} to copy its {@link ProofEnvironment}.
    * @return The created {@link ProofEnvironment} which is a copy of the environment of the given {@link Proof} but with its own {@link OneStepSimplifier} instance.
    */
   public static ProofEnvironment cloneProofEnvironmentWithOwnOneStepSimplifier(final Proof source, final boolean useSimplifyTermProfile) {
      assert source != null;
      assert !source.isDisposed();
      return cloneProofEnvironmentWithOwnOneStepSimplifier(source.getInitConfig(), useSimplifyTermProfile);
   }
   
   /**
    * Creates a copy of the {@link ProofEnvironment} of the given {@link Proof}
    * which has his own {@link OneStepSimplifier} instance. Such copies are
    * required for instance during parallel usage of site proofs because
    * {@link OneStepSimplifier} has an internal state.
    * @param sourceInitConfig The {@link InitConfig} to copy its {@link ProofEnvironment}.
    * @return The created {@link ProofEnvironment} which is a copy of the environment of the given {@link Proof} but with its own {@link OneStepSimplifier} instance.
    */
   @SuppressWarnings("unchecked")
public static ProofEnvironment cloneProofEnvironmentWithOwnOneStepSimplifier(final InitConfig sourceInitConfig, final boolean useSimplifyTermProfile) {
      // Get required source instances
      final RuleJustificationInfo sourceJustiInfo = sourceInitConfig.getJustifInfo();
      // Create new profile which has separate OneStepSimplifier instance
      JavaProfile profile;
      if (useSimplifyTermProfile) {
         profile = new SimplifyTermProfile() {
            @Override
            protected ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration() {
               Profile sourceProfile = sourceInitConfig.getProfile();
               if (sourceProfile instanceof SymbolicExecutionJavaProfile) {
                  ImmutableList<TermLabelConfiguration> result = super.computeTermLabelConfiguration();
                  result = result.prepend(SymbolicExecutionJavaProfile.getSymbolicExecutionTermLabelConfigurations(SymbolicExecutionJavaProfile.isTruthValueEvaluationEnabled(sourceInitConfig))); // Make sure that the term labels of symbolic execution are also supported by the new environment.
                  return result;
               }
               else {
                  return super.computeTermLabelConfiguration();
               }
            }
         };
      }
      else {
         profile = new JavaProfile() {
            @Override
            protected ImmutableList<TermLabelConfiguration> computeTermLabelConfiguration() {
               Profile sourceProfile = sourceInitConfig.getProfile();
               if (sourceProfile instanceof SymbolicExecutionJavaProfile) {
                  ImmutableList<TermLabelConfiguration> result = super.computeTermLabelConfiguration();
                  result = result.prepend(SymbolicExecutionJavaProfile.getSymbolicExecutionTermLabelConfigurations(SymbolicExecutionJavaProfile.isTruthValueEvaluationEnabled(sourceInitConfig))); // Make sure that the term labels of symbolic execution are also supported by the new environment.
                  return result;
               }
               else {
                  return super.computeTermLabelConfiguration();
               }
            }
         };
      }
      // Create new InitConfig
      final InitConfig initConfig = new InitConfig(sourceInitConfig.getServices().copy(profile, false));
      // Set modified taclet options in which runtime exceptions are banned.
      Choice runtimeExceptionTreatment = new Choice("ban", "runtimeExceptions");
      ImmutableSet<Choice> choices = SideProofUtil.activateChoice(sourceInitConfig.getActivatedChoices(), 
              runtimeExceptionTreatment);
      initConfig.setActivatedChoices(choices);
      // Initialize InitConfig with settings from the original InitConfig.
      final ProofSettings clonedSettings = sourceInitConfig.getSettings() != null ? new ProofSettings(sourceInitConfig.getSettings()) : null;
      initConfig.setSettings(clonedSettings);
      initConfig.setTaclet2Builder((HashMap<Taclet, TacletBuilder<? extends Taclet>>) sourceInitConfig.getTaclet2Builder().clone());
      initConfig.setTaclets(sourceInitConfig.getTaclets());
      // Create new ProofEnvironment and initialize it with values from initial one.
      ProofEnvironment env = new ProofEnvironment(initConfig);
      for (Taclet taclet : initConfig.activatedTaclets()) {
         initConfig.getJustifInfo().addJustification(taclet, sourceJustiInfo.getJustification(taclet));
      }
      for (BuiltInRule rule : initConfig.builtInRules()) {
         RuleJustification origJusti = sourceJustiInfo.getJustification(rule);
         if (origJusti == null) {
            assert rule instanceof OneStepSimplifier;
            origJusti = AxiomJustification.INSTANCE;
         }
         initConfig.getJustifInfo().addJustification(rule, origJusti);
      }
      return env;
   }

   /**
    * <p>
    * Stores or disposes the {@link Proof} of the {@link ApplyStrategyInfo} in {@link SideProofStore#DEFAULT_INSTANCE}.
    * </p>
    * <p>
    * This method should be called whenever a side proof is no longer needed
    * and should be disposed or stored for debugging purposes.
    * </p>
    * @param description The description.
    * @param info The {@link ApplyStrategyInfo} to store or dispose its {@link Proof}.
    */
   public static void disposeOrStore(String description, ApplyStrategyInfo info) {
      if (info != null) {
         if (SideProofStore.DEFAULT_INSTANCE.isEnabled()) {
            SideProofStore.DEFAULT_INSTANCE.addProof(description, info.getProof());
         }
         else {
            info.getProof().dispose();
         }
      }
   }
}
