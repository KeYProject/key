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

package de.uka.ilkd.key.symbolic_execution;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.AbstractSymbolicAssociationValueContainer;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.ModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicState;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.ProofStarter;

/**
 * <p>
 * Instances of this class can be used to compute memory layouts
 * (objects with values and associations to other objects on the heap together
 * with objects and associations to objects on the current state of the stack)
 * which a given {@link Node} of KeY's proof tree can have based on 
 * equivalence classes (aliasing) of objects.
 * Such memory layouts are named <i>current memory layouts</i>. It is also possible
 * to compute how the heap and stack was when the proof was started. Such
 * memory layouts are named <i>initial memory layouts</i>. 
 * </p>
 * <p>
 * Example program:
 * <pre><code>
 * public class Example {
 *    private int value;
 *    
 *    private Example next;
 *    
 *    public static int main(Example e) {
 *       e.value = 1;
 *       e.next.value = 2;
 *       return e.value + e.next.value; // Current node in KeY's proof tree
 *    }
 * }
 * </code></pre>
 * If the symbolic execution stops at the return statement, 
 * two memory layouts are possible. In the first case refers
 * {@code e} and {@code e.next} to different objects (result is {@code 3}). 
 * In the second case refers both to the same object (result is {@code 4}).
 * That both objects can't be {@code null} is ensured by the path condition from root to the current node in KeY's proof tree.
 * </p>
 * <p>
 * The following code snippet shows how to use this class:
 * <pre><code>
 * SymbolicLayoutExtractor e = new SymbolicLayoutExtractor(node);
 * e.analyse();
 * for (int i = 0; i < e.getLayoutsCount(); i++) {
 *    ImmutableList&lt;ISymbolicEquivalenceClass&gt; equivalenceClasses = e.getEquivalenceClasses(i);
 *    ISymbolicLayout initial = e.getInitialLayout(i);
 *    ISymbolicLayout current = e.getCurrentLayout(i);
 * }
 * </code></pre>
 * </p>
 * <p>
 * Rough description of the implemented algorithm:
 * <ol>
 *    <li>
 *       Compute possible equivalence classes which leads to different memory layouts via {@link #analyse()}.
 *       <ol>
 *          <li>
 *             Compute path condition from root to the node for which memory layouts should be build.
 *          </li>
 *          <li>
 *             Compute locations (values/associations of objects and state) to show later in initial and current memory layouts.
 *             Initial locations are extracted from path condition and conditions of node's sequent.
 *             Current locations are all initial locations plus locations defined in updates of node's sequent.
 *             The location of the exc variable and backup of initial method arguments and the heap of the initial proof obligation are ignored.
 *             Objects of updates created during symbolic execution and objects of the right site of updates are also collected.
 *          </li>
 *          <li>
 *             Compute objects which should be checked for equality (aliasing). The Set consists of objects from path condition,
 *             objects on the right side of updates, objects in conditions of node's antecedent and null.
 *          </li>
 *          <li>
 *             Create a site proof which starts in a modified version of the root node. 
 *             It contains the given path condition as additional antecedent and the modality with he java code is removed.
 *             Cut rules are applied to this sequent for each possible combination of two different objects. 
 *             Each goal represents a memory layout and the applied cuts in each goal represents the equality classes.
 *          </li>
 *          <li>
 *             Create a predicate which is used to compute the objects, values and associations of an initial/a current memory layout.
 *             Objects are represented as expressions like {@code e} or {@code e.next}. The problem is that in a current memory layout the
 *             object structure might have changed and {@code e.next} is a different object compared to the initial memory layout. 
 *             To solve this issue is an additional update is used which stores each object in a temporary program variable, e.g.
 *             {@code pre0 = e}, {@code pre1 = e.next}. This makes sure that the objects are the same in initial and current memory layouts.
 *          </li>
 *       </ol>
 *    </li>
 *    <li>
 *       Compute a concrete initial or current memory layout when they are requested the first time via {@link #lazyComputeLayout(Node, ImmutableSet, Term, Set, ImmutableList, Term, String)}.
 *       <ol>
 *          <li>
 *             Start side proof based on node's sequent for a current memory layout or root's sequent for an initial memory layout.
 *             The sequent is modified by adding the pre updates and on initial memory layouts also the path condition.
 *             The equivalence classes are added and the modality is replaced with the predicate to compute objects, values and associations.
 *          </li>
 *          <li>
 *             Extract values from the predicate.
 *          </li>
 *          <li>
 *             Create new {@link ISymbolicLayout} and fill it with objects, values and associations from the extracted values of the side proof.
 *          </li>
 *       </ol>
 *    </li>
 * </ol>
 * </p>
 * @author Martin Hentschel
 * @see ISymbolicLayout
 * @see ExecutionNodeSymbolicLayoutExtractor
 */
public class SymbolicLayoutExtractor extends AbstractUpdateExtractor {   
   /**
    * The used {@link IModelSettings}.
    */
   private final IModelSettings settings;
   
   /**
    * Contains the applied cuts of each possible memory layout.
    * An applied cut is represented as {@link Term} of the from
    * {@code equals(obj1, obj2)} or {@code not(equals(obj1, obj2))}.
    */
   private List<ImmutableSet<Term>> appliedCutsPerLayout;
   
   /**
    * Contains the current memory layouts accessible via {@link #getCurrentLayout(int)}.
    */
   private Map<Integer, ISymbolicLayout> currentLayouts;
   
   /**
    * The {@link ExtractLocationParameter} instances used to compute a current memory layout.
    */
   private Set<ExtractLocationParameter> currentLocations;
   
   /**
    * The term with the result predicate used to compute the values of locations
    * shown in a current memory layout.
    */
   private Term currentLocationTerm;
   
   /**
    * Contains the initial memory layouts accessible via {@link #getInitialLayout(int)}.
    */
   private Map<Integer, ISymbolicLayout> initialLayouts;
   
   /**
    * The {@link ExtractLocationParameter} instances used to compute an initial memory layout.
    */
   private Set<ExtractLocationParameter> initialLocations;
   
   /**
    * The term with the result predicate used to compute the values of locations
    * shown in an initial memory layout.
    */
   private Term initialLocationTerm;
   
   /**
    * Contains the equivalent classes accessible via {@link #getEquivalenceClasses(int)}.
    */
   private Map<Integer, ImmutableList<ISymbolicEquivalenceClass>> layoutsEquivalentClasses;
   
   /**
    * Contains objects which should be ignored in the state because they
    * are created during symbolic execution or part of the proof obligation.
    */
   private Set<Term> objectsToIgnore;
   
   /**
    * Constructor.
    * @param node The {@link Node} of KeY's proof tree to compute memory layouts for.
    * @param modalityPio The {@link PosInOccurrence} of the modality or its updates.
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public SymbolicLayoutExtractor(Node node, 
                                  PosInOccurrence modalityPio,
                                  boolean useUnicode,
                                  boolean usePrettyPrinting) {
      super(node, modalityPio);
      this.settings = new ModelSettings(useUnicode, usePrettyPrinting);
   }

   /**
    * <p>
    * Computes the possible memory layouts.
    * </p>
    * <p>
    * This is the prerequisite to access equivalence classes, initial
    * and current states.
    * </p>
    * @throws ProofInputException Occurred Exception.
    */
   public void analyse() throws ProofInputException {
      synchronized (this) {
         if (!isAnalysed()) {
            // Get path condition
            Term pathCondition = SymbolicExecutionUtil.computePathCondition(node, false);
            pathCondition = removeImplicitSubTermsFromPathCondition(pathCondition);
            // Compute all locations used in path conditions and updates. The values of the locations will be later computed in the state computation (and finally shown in a memory layout).
            Set<ExtractLocationParameter> temporaryCurrentLocations = new LinkedHashSet<ExtractLocationParameter>();
            objectsToIgnore = computeInitialObjectsToIgnore(); // Contains all objects which should be ignored, like exc of the proof obligation and created objects during symbolic execution
            Set<Term> updateCreatedObjects = new LinkedHashSet<Term>(); // Contains all objects which are created during symbolic execution
            Set<Term> updateValueObjects = new LinkedHashSet<Term>(); // Contains all objects which are the value of an update
            collectLocationsFromUpdates(node.sequent(), temporaryCurrentLocations, updateCreatedObjects, updateValueObjects, objectsToIgnore);
            objectsToIgnore.addAll(updateCreatedObjects);
            initialLocations = extractLocationsFromTerm(pathCondition, objectsToIgnore);
            initialLocations.addAll(extractLocationsFromSequent(node.sequent(), objectsToIgnore));
            currentLocations = new LinkedHashSet<ExtractLocationParameter>(initialLocations);
            currentLocations.addAll(temporaryCurrentLocations);
            // Compute objects for equivalence check.
            Set<Term> symbolicObjectsResultingInCurrentState = new LinkedHashSet<Term>();
            symbolicObjectsResultingInCurrentState.addAll(filterOutObjectsToIgnore(updateValueObjects, objectsToIgnore));
            symbolicObjectsResultingInCurrentState.addAll(collectObjectsFromSequent(node.sequent(), objectsToIgnore));
            symbolicObjectsResultingInCurrentState = sortTerms(symbolicObjectsResultingInCurrentState); // Sort terms alphabetically. This guarantees that in equivalence classes the representative term is for instance self.next and not self.next.next.
            symbolicObjectsResultingInCurrentState.add(getServices().getTermBuilder().NULL()); // Add null because it can happen that a object is null and this option must be included in equivalence class computation
            // Compute a Sequent with the initial conditions of the proof without modality
            Sequent initialConditionsSequent = createSequentForEquivalenceClassComputation();
            ApplyStrategyInfo info = null;
            try {
               // Instantiate proof in which equivalent classes of symbolic objects are computed.
               ProofStarter equivalentClassesProofStarter = SideProofUtil.createSideProof(getProof(), initialConditionsSequent, true);
               // Apply cut rules to compute equivalent classes
               applyCutRules(equivalentClassesProofStarter, symbolicObjectsResultingInCurrentState);
               // Finish proof automatically
               info = SideProofUtil.startSideProof(getProof(), 
                                                   equivalentClassesProofStarter, 
                                                   StrategyProperties.METHOD_CONTRACT,
                                                   StrategyProperties.LOOP_INVARIANT,
                                                   StrategyProperties.QUERY_ON,
                                                   StrategyProperties.SPLITTING_NORMAL);
               // Compute the available instance memory layout via the opened goals of the equivalent proof.
               appliedCutsPerLayout = extractAppliedCutsFromGoals(equivalentClassesProofStarter.getProof());
               // Create predicate required for state computation
               initialLocationTerm = createLocationPredicateAndTerm(initialLocations);
               currentLocationTerm = createLocationPredicateAndTerm(currentLocations);
               // Create memory layout maps which are filled lazily
               initialLayouts = new LinkedHashMap<Integer, ISymbolicLayout>(appliedCutsPerLayout.size());
               currentLayouts = new LinkedHashMap<Integer, ISymbolicLayout>(appliedCutsPerLayout.size());
               layoutsEquivalentClasses = new LinkedHashMap<Integer, ImmutableList<ISymbolicEquivalenceClass>>();
            }
            finally {
               SideProofUtil.disposeOrStore("Equivalence class computation on node " + node.serialNr() + ".", info);
            }
         }
      }
   }
   
   /**
    * Sorts the given {@link Term}s alphabetically.
    * @param terms The {@link Term}s to sort.
    * @return The sorted {@link Term}s.
    */
   protected Set<Term> sortTerms(Set<Term> terms) {
      List<Term> list = new LinkedList<Term>(terms);
      Collections.sort(list, new Comparator<Term>() {
         @Override
         public int compare(Term o1, Term o2) {
            String o1s = o1.toString();
            String o2s = o2.toString();
            return o1s.length() - o2s.length();
         }
      });
      return new LinkedHashSet<Term>(list);
   }

   /**
    * Filters out the objects from the second {@link Set} in the first {@link Set}.
    * @param objectsToFilter The {@link Set} to filter.
    * @param objectsToIgnore The {@link Set} with the objects to filter out.
    * @return A new {@link Set} which contains all objects of the first {@link Set} which are not contained in the second {@link Set}.
    * @throws ProofInputException
    */
   protected Set<Term> filterOutObjectsToIgnore(Set<Term> objectsToFilter, 
                                                Set<Term> objectsToIgnore) throws ProofInputException {
      Set<Term> result = new LinkedHashSet<Term>();
      for (Term symbolicObject : objectsToFilter) {
         if (!objectsToIgnore.contains(symbolicObject)) {
            result.add(symbolicObject);
         }
      }
      return result;
   }
   
   /**
    * <p>
    * Creates a {@link Sequent} which is used to compute equivalence classes.
    * </p>
    * <p>
    * The created {@link Sequent} is the {@link Sequent} of {@link #node}
    * without the modality.
    * </p>
    * @return The created {@link Sequent} to use for equivalence class computation.
    */
   protected Sequent createSequentForEquivalenceClassComputation() {
      return SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, 
                                                                        modalityPio, 
                                                                        null,
                                                                        null,
                                                                        null,
                                                                        false);
   }
   
   /**
    * <p>
    * Applies cut rules to the given side proofs to compute equivalence classes.
    * </p>
    * <p>
    * For each possible combination (without identity and ignoring the order) of the given objects is one cut performed.
    * </p>
    * @param starter The {@link ProofStarter} which provides the side proof.
    * @param symbolicObjects The symbolic objects to compute equivalence classes for.
    */
   protected void applyCutRules(ProofStarter starter, Set<Term> symbolicObjects) {
      List<Term> objectsCopy = new ArrayList<Term>(symbolicObjects);
      int maxProofSteps = 8000;
      for (int i = 0; i < objectsCopy.size(); i++) {
         for (int j = i + 1; j < objectsCopy.size(); j++) {
            Term equalTerm = getServices().getTermBuilder().equals(objectsCopy.get(i), objectsCopy.get(j));
            applyCut(starter, equalTerm, maxProofSteps);
         }
      }
      starter.setMaxRuleApplications(maxProofSteps);
      starter.start();
   }

   /**
    * Applies one single cut rule for the given {@link Term}.
    * @param starter The {@link ProofStarter} to apply cut rule in.
    * @param term The {@link Term} to cut out.
    * @param maxProofSteps The maximal number of proof steps applied after cut via auto mode.
    */
   protected void applyCut(ProofStarter starter, Term term, int maxProofSteps) {
      ImmutableList<Goal> goals = starter.getProof().openEnabledGoals();
      if (!goals.isEmpty()) {
         int proofSteps = maxProofSteps / goals.size();
         if (proofSteps < 300) {
            proofSteps = 300;
         }
         starter.setMaxRuleApplications(maxProofSteps);
         for (final Goal g : goals) {
            final NoPosTacletApp c = g.indexOfTaclets().lookup("cut");
            assert c != null;

            ImmutableSet<SchemaVariable> set2 = c.uninstantiatedVars();
            SchemaVariable cutF = set2.iterator().next();

            TacletApp t2 = c.addInstantiation(cutF, term, false, getServices());

            final ImmutableList<Goal> branches = g.apply(t2);
            starter.start(branches);
        }
      }
   }

   /**
    * <p>
    * Extracts the possible memory layouts from the given side proof.
    * Each open {@link Goal} of the proof results in its own memory layout.
    * </p>
    * <p>
    * The applied cuts per memory layout are represented as {@link Term} 
    * stored in the {@link ImmutableSet}s. Each {@link Term} has the form
    * {@code equals(obj1, obj2)} or {@code not(equals(obj1, obj2))}
    * </p>
    * @param proof The {@link Proof} which provides the {@link Goal}s to extract memory layouts from.
    * @return Each entry in the list represents a equivalence class memory layout. For each object pair checked via cut rules application exists one entry in the {@link Set} of the form {@code equals(obj1, obj2)} or {@code not(equals(obj1, obj2))}.
    * @throws ProofInputException Occurred Exception.
    */
   protected List<ImmutableSet<Term>> extractAppliedCutsFromGoals(Proof proof) throws ProofInputException {
      Set<ImmutableSet<Term>> resultSet = new LinkedHashSet<ImmutableSet<Term>>();
      Node root = proof.root();
      for (Goal goal : proof.openGoals()) {
         resultSet.add(extractAppliedCutsSet(goal.node(), root));
      }
      return new ArrayList<ImmutableSet<Term>>(resultSet);
   }
   
   /**
    * Extracts the applied cut rules in the given {@link Node}. Each cut
    * rule is represented as {@link Term} of the form {@code equals(obj1, obj2)} or {@code not(equals(obj1, obj2))}.
    * @param goalnode The current {@link Node}.
    * @param root The root {@link Node}.
    * @return The applied cut rules.
    * @throws ProofInputException Occurred Exception.
    */
   protected ImmutableSet<Term> extractAppliedCutsSet(Node goalnode, Node root) throws ProofInputException {
      ImmutableSet<Term> result = DefaultImmutableSet.<Term> nil();
      if (!root.find(goalnode)) {
         throw new ProofInputException("Node \"" + goalnode + "\" ist not a childs of root node \"" + root + "\".");
      }
      while (!(goalnode.serialNr() == root.serialNr())) {
         final Node oldNode = goalnode;
         goalnode = goalnode.parent();
         if (goalnode.getAppliedRuleApp() instanceof NoPosTacletApp) {
            NoPosTacletApp npta = (NoPosTacletApp) goalnode.getAppliedRuleApp();
            if ("CUT".equals(npta.taclet().name().toString().toUpperCase())) {
               Term inst = (Term) npta.instantiations().lookupEntryForSV(new Name("cutFormula")).value().getInstantiation();
               if (goalnode.child(1) == oldNode) {
                  inst = getServices().getTermBuilder().not(inst);
               }
               result = result.add(inst);
            }
         }
      }
      return result;
   }

   /**
    * Checks if {@link #analyse()} was already executed.
    * @return {@code true} {@link #analyse()} was executed, {@code false} {@link #analyse()} was not executed.
    */
   public boolean isAnalysed() {
      synchronized (this) {
         return initialLayouts != null && currentLayouts != null;
      }
   }

   /**
    * <p>
    * Returns the number of available memory layouts.
    * </p>
    * <p>
    * <b>Attention:</b> Requires that {@link #analyse()} was executed. 
    * </p>
    * @return The number of available memory layouts.
    */
   public int getLayoutsCount() {
      synchronized (this) {
         assert isAnalysed();
         return appliedCutsPerLayout.size();
      }
   }
   
   /**
    * <p>
    * Returns the initial memory layout at the given index.
    * </p>
    * <p>
    * <b>Attention:</b> Requires that {@link #analyse()} was executed. 
    * </p>
    * @param layoutIndex The index of the initial memory layout.
    * @return The initial memory layout at the given index. 
    * @throws ProofInputException Occurred Exception
    */
   public ISymbolicLayout getInitialLayout(int layoutIndex) throws ProofInputException {
      return getLayout(initialLayouts, layoutIndex, initialLocationTerm, initialLocations, computeInitialStateName(), false);
   }

   /**
    * Computes the state name of an initial memory layout.
    * @return The state name of an initial memory layout.
    */
   protected String computeInitialStateName() {
      return getRoot().name() + " resulting in " + computeCurrentStateName();
   }

   /**
    * <p>
    * Returns the current memory layout at the given index.
    * </p>
    * <p>
    * <b>Attention:</b> Requires that {@link #analyse()} was executed. 
    * </p>
    * @param layoutIndex The index of the current memory layout.
    * @return The current memory layout at the given index. 
    * @throws ProofInputException Occurred Exception
    */
   public ISymbolicLayout getCurrentLayout(int layoutIndex) throws ProofInputException {
      return getLayout(currentLayouts, layoutIndex, currentLocationTerm, currentLocations, computeCurrentStateName(), true);
   }
   
   /**
    * Computes the state name of a current memory layout.
    * @return The state name of a current memory layout.
    */
   protected String computeCurrentStateName() {
      return node.name();
   }

   /**
    * Helper method of {@link #getInitialLayout(int)} and
    * {@link #getCurrentLayout(int)} to lazily compute and get a memory layout.
    * @param confiurationsMap The map which contains already computed memory layouts.
    * @param layoutIndex The index of the memory layout to lazily compute and return.
    * @param layoutTerm The result term to use in side proof.
    * @param locations The locations to compute in side proof.
    * @param stateName The name of the state.
    * @param currentLayout {@code true} current layout, {@code false} initial layout.
    * @return The lazily computed memory layout.
    * @throws ProofInputException Occurred Exception.
    */
   protected ISymbolicLayout getLayout(Map<Integer, ISymbolicLayout> confiurationsMap, 
                                       int layoutIndex,
                                       Term layoutTerm,
                                       Set<ExtractLocationParameter> locations,
                                       String stateName,
                                       boolean currentLayout) throws ProofInputException {
      synchronized (this) {
         assert layoutIndex >= 0;
         assert layoutIndex < appliedCutsPerLayout.size();
         assert isAnalysed();
         ISymbolicLayout result = confiurationsMap.get(Integer.valueOf(layoutIndex));
         if (result == null) {
            // Get memory layout
            ImmutableSet<Term> layout = appliedCutsPerLayout.get(layoutIndex);
            ImmutableList<ISymbolicEquivalenceClass> equivalentClasses = getEquivalenceClasses(layoutIndex);
            result = lazyComputeLayout(layout, layoutTerm, locations, equivalentClasses, stateName, currentLayout);
            confiurationsMap.put(Integer.valueOf(layoutIndex), result);
         }
         return result;
      }
   }
   
   /**
    * <p>
    * Computes a memory layout lazily when it is first time requested via 
    * {@link #getLayout(Map, int, Term, Set, String, boolean)}.
    * </p>
    * <p>
    * Finally, the last step is to create the {@link ISymbolicLayout} instance
    * and to fill it with the values/associations defined by {@link ExecutionVariableValuePair} instances.
    * </p>
    * @param layout The memory layout terms.
    * @param layoutTerm The result term to use in side proof.
    * @param locations The locations to compute in side proof.
    * @param equivalentClasses The equivalence classes defined by the memory layout terms.
    * @param stateName The name of the state.
    * @param currentLayout {@code true} current layout, {@code false} initial layout.
    * @return The created memory layout.
    * @throws ProofInputException Occurred Exception.
    */
   protected ISymbolicLayout lazyComputeLayout(ImmutableSet<Term> layout, 
                                               Term layoutTerm,
                                               Set<ExtractLocationParameter> locations,
                                               ImmutableList<ISymbolicEquivalenceClass> equivalentClasses,
                                               String stateName,
                                               boolean currentLayout) throws ProofInputException {
      if (!locations.isEmpty()) {
         Term layoutCondition = getServices().getTermBuilder().and(layout);
         Set<ExecutionVariableValuePair> pairs = computeVariableValuePairs(layoutCondition, layoutTerm, locations, currentLayout);
         return createLayoutFromExecutionVariableValuePairs(equivalentClasses, pairs, stateName);
      }
      else {
         return createLayoutFromExecutionVariableValuePairs(equivalentClasses, new LinkedHashSet<ExecutionVariableValuePair>(), stateName);
      }
   }

   /**
    * Collects all objects which are used in the conditions of the {@link Sequent}.
    * @param sequent The {@link Sequent} which provides the conditions to collect objects from.
    * @param objectsToIgnore Objects which should be excluded in the result.
    * @return The found objects.
    * @throws ProofInputException Occurred Exception.
    */
   protected Set<Term> collectObjectsFromSequent(Sequent sequent,
                                                 Set<Term> objectsToIgnore) throws ProofInputException {
      Set<Term> result = new LinkedHashSet<Term>();
      for (SequentFormula sf : sequent) {
         if (SymbolicExecutionUtil.checkSkolemEquality(sf) == 0) {
            result.addAll(collectSymbolicObjectsFromTerm(sf.formula(), objectsToIgnore));
         }
      }
      return result;
   }
   
   /**
    * Collects all objects which are used in the given {@link Term}.
    * @param term The {@link Term} to collect objects in.
    * @param objectsToIgnore Objects which should be excluded in the result.
    * @return The found objects.
    * @throws ProofInputException Occurred Exception.
    */
   protected Set<Term> collectSymbolicObjectsFromTerm(Term term, 
                                                      final Set<Term> objectsToIgnore) throws ProofInputException {
      final Set<Term> result = new LinkedHashSet<Term>();
      term.execPreOrder(new DefaultVisitor() {
         @Override
         public void visit(Term visited) {
            if (SymbolicExecutionUtil.hasReferenceSort(getServices(), visited) && 
                visited.freeVars().isEmpty() &&
                !objectsToIgnore.contains(visited) &&
                !SymbolicExecutionUtil.isSkolemConstant(visited)) {
               result.add(visited);
            }
         }
      });
      return result;
   }
   
   /**
    * <p>
    * Returns the equivalence class of the memory layout defined by the index.
    * </p>
    * <p>
    * <b>Attention:</b> Requires that {@link #analyse()} was executed. 
    * </p>
    * @param layoutIndex The index of the memory layout to get its equivalence classes.
    * @return The equivalence classes of the memory layout at the given index.
    */
   public ImmutableList<ISymbolicEquivalenceClass> getEquivalenceClasses(int layoutIndex) {
      synchronized (this) {
         ImmutableList<ISymbolicEquivalenceClass> equivalentClasses = layoutsEquivalentClasses.get(Integer.valueOf(layoutIndex));
         if (equivalentClasses == null) {
            ImmutableSet<Term> appliedCuts = appliedCutsPerLayout.get(layoutIndex);
            equivalentClasses = lazyComputeEquivalenzClasses(appliedCuts);
            layoutsEquivalentClasses.put(Integer.valueOf(layoutIndex), equivalentClasses);
         }
         return equivalentClasses;
      }
   }

   /**
    * <p>
    * Computes the equivalence classes from the given applied cut rules
    * lazily when {@link #getEquivalenceClasses(int)} is called the first time.
    * </p>
    * <p>
    * Each entry in the given {@link ImmutableSet} is of the form
    * {@code equals(obj1, obj2)} or {@code not(equals(obj1, obj2))}.
    * </p>
    * <p>
    * An {@link ISymbolicEquivalenceClass} is only created for objects which
    * are equal. Objects which are equal to no other one are not represented
    * in an {@link ISymbolicEquivalenceClass}. This makes sure that each
    * {@link ISymbolicEquivalenceClass} contains at least two objects and
    * that the result is empty if all objects are not equal to each other.
    * </p>
    * @param appliedCuts The applied cut rules.
    * @return The created {@link ISymbolicEquivalenceClass} instances.
    */
   protected ImmutableList<ISymbolicEquivalenceClass> lazyComputeEquivalenzClasses(ImmutableSet<Term> appliedCuts) {
      ImmutableList<ISymbolicEquivalenceClass> result = ImmutableSLList.nil();
      for (Term term : appliedCuts) {
         if (Junctor.NOT != term.op()) {
            assert term.op() == Equality.EQUALS;
            final Iterator<Term> iter = term.subs().iterator();
            ISymbolicEquivalenceClass ec = null;
            while (ec == null && iter.hasNext()) {
               ec = findEquivalentClass(result, iter.next());
            }
            if (ec == null) {
               ec = new SymbolicEquivalenceClass(getServices(), settings);
               result = result.append(ec); 
            }
            for (Term sub : term.subs()) {
               if (!ec.containsTerm(sub)) {
                  ((SymbolicEquivalenceClass)ec).addTerm(sub);
               }
            }
         }
      }
      return result;
   }
   
   /**
    * Searches the {@link ISymbolicEquivalenceClass} from the given one
    * which contains the given {@link Term}.
    * @param equivalentClasses The available {@link ISymbolicEquivalenceClass} to search in.
    * @param term The {@link Term} to search.
    * @return The found {@link ISymbolicEquivalenceClass} which contains the given {@link Term} or {@code null} if no one was found.
    */
   protected ISymbolicEquivalenceClass findEquivalentClass(ImmutableList<ISymbolicEquivalenceClass> equivalentClasses, 
                                                           final Term term) {
      return JavaUtil.search(equivalentClasses, new IFilter<ISymbolicEquivalenceClass>() {
         @Override
         public boolean select(ISymbolicEquivalenceClass element) {
            return element.containsTerm(term);
         }
      });
   }
   
   /**
    * Creates an {@link ISymbolicLayout} which shows the objects,
    * values and associations defined by the given {@link ExecutionVariableValuePair}s.
    * @param equivalentClasses The used {@link ISymbolicEquivalenceClass} instances of the memory layout.
    * @param pairs Provides the available objects, their values and associations together with the variables and association of the state.
    * @param stateName The name of the state.
    * @return The created {@link ISymbolicLayout} with the given content.
    * @throws ProofInputException Occurred Exception.
    */
   protected ISymbolicLayout createLayoutFromExecutionVariableValuePairs(ImmutableList<ISymbolicEquivalenceClass> equivalentClasses, 
                                                                         Set<ExecutionVariableValuePair> pairs,
                                                                         String stateName) throws ProofInputException {
      SymbolicLayout result = new SymbolicLayout(settings, equivalentClasses);
      // Create state
      SymbolicState state = new SymbolicState(stateName, settings);
      result.setState(state);
      // Create objects
      Map<Term, SymbolicObject> objects = new LinkedHashMap<Term, SymbolicObject>();
      for (ExecutionVariableValuePair pair : pairs) {
         // Create object for parent of current value
         createObjectForTerm(objects, equivalentClasses, result, pair.getParent());
         // Create object for current value
         createObjectForTerm(objects, equivalentClasses, result, pair.getValue());
      }
      // Fill objects and state with association and values
      for (ExecutionVariableValuePair pair : pairs) {
         // Find parent object/state
         Term parent = pair.getParent();
         Term valueTerm = pair.getValue();
         AbstractSymbolicAssociationValueContainer container;
         if (parent != null) {
            ISymbolicEquivalenceClass equivalentClass = findEquivalentClass(equivalentClasses, parent);
            container = objects.get(equivalentClass != null ? equivalentClass.getRepresentative() : parent);
         }
         else {
            if (pair.isStateMember() || !objectsToIgnore.contains(valueTerm)) {
               container = state; // Add only updates of local variables to the  
            }
            else {
               container = null;
            }
         }
         // Check if a container was found, if not it is an less important equivalent object
         if (container != null) {
            // Check if the term is in an equivalent class, in this case use the representative term instead of the term itself.
            ISymbolicEquivalenceClass eq = findEquivalentClass(equivalentClasses, valueTerm);
            if (eq != null) {
               valueTerm = eq.getRepresentative();
            }
            // Check if it is an association
            SymbolicObject target = objects.get(valueTerm);
            if (target != null) {
               SymbolicAssociation association;
               if (pair.isArrayIndex()) {
                  association = new SymbolicAssociation(getServices(), pair.getArrayIndex(), target, pair.getCondition(), settings);
               }
               else {
                  association = new SymbolicAssociation(getServices(), pair.getProgramVariable(), target, pair.getCondition(), settings);
               }
               // Add association only if not already present
               ISymbolicAssociation existingAssociation = container.getAssociation(association.getProgramVariable(), association.isArrayIndex(), association.getArrayIndex(), association.getCondition());
               if (existingAssociation == null) {
                  // Add association to the container
                  container.addAssociation(association);
               }
               else {
                  // Make sure that target is the same
                  if (!JavaUtil.equals(association.getTarget(), existingAssociation.getTarget())) {
                     throw new ProofInputException("Multiple association targets found: " + association + " and " + existingAssociation + ".");
                  }
               }
            }
            else {
               SymbolicValue value;
               if (pair.isArrayIndex()) {
                  value = new SymbolicValue(getServices(), pair.getArrayIndex(), valueTerm, pair.getCondition(), settings);
               }
               else {
                  value = new SymbolicValue(getServices(), pair.getProgramVariable(), valueTerm, pair.getCondition(), settings);
               }
               // Add value only if not already present
               ISymbolicValue existingValue = container.getValue(value.getProgramVariable(), value.isArrayIndex(), value.getArrayIndex(), value.getCondition());
               if (existingValue == null) {
                  // Add value to the container
                  container.addValue(value);
               }
               else {
                  // Make sure that the value is the same
                  if (!JavaUtil.equals(value.getValue(), existingValue.getValue())) {
                     throw new ProofInputException("Multiple values found: " + value + " and " + existingValue + ".");
                  }
               }
            }
         }
      }
      return result;
   }

   /**
    * Creates for the object defined by the given {@link Term} an {@link SymbolicObject} instance if not already available.
    * @param objects The already available {@link SymbolicObject}s.
    * @param equivalentClasses The available {@link ISymbolicEquivalenceClass}.
    * @param result The {@link SymbolicLayout} to add the {@link SymbolicObject} to.
    * @param objectTerm The {@link Term} which represents the {@link Object} a {@link SymbolicObject} should be created for.
    */
   protected void createObjectForTerm(Map<Term, SymbolicObject> objects,
                                      ImmutableList<ISymbolicEquivalenceClass> equivalentClasses,
                                      SymbolicLayout result,
                                      Term objectTerm) {
      if (objectTerm != null && SymbolicExecutionUtil.hasReferenceSort(getServices(), objectTerm)) {
         ISymbolicEquivalenceClass equivalentClass = findEquivalentClass(equivalentClasses, objectTerm);
         if (equivalentClass != null) {
            objectTerm = equivalentClass.getRepresentative();
         }
         SymbolicObject object = objects.get(objectTerm);
         if (object == null) {
            object = new SymbolicObject(getServices(), objectTerm, settings);
            objects.put(objectTerm, object);
            result.addObject(object);
         }
      }
   }
}