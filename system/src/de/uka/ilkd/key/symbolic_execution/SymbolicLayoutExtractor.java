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
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
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
public class SymbolicLayoutExtractor {
   /**
    * Contains the {@link Node} of KeY's proof tree to compute memory layouts for.
    */
   private final Node node;
   
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
    * An incremented number used to give each pre value an unique name.
    */
   private int preVariableIndex = 0;
   
   /**
    * The complete path condition which defines how to reach {@link #node} from the root of the proof.
    */
   private Term pathCondition;
   
   /**
    * Contains objects which should be ignored in the state because they
    * are created during symbolic execution or part of the proof obligation.
    */
   private Set<Term> objectsToIgnore;
   
   /**
    * Constructor.
    * @param node The {@link Node} of KeY's proof tree to compute memory layouts for.
    * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode characters.
    * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty printing.
    */
   public SymbolicLayoutExtractor(Node node, 
                                  boolean useUnicode,
                                  boolean usePrettyPrinting) {
      assert node != null;
      this.node = node;
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
            pathCondition = SymbolicExecutionUtil.computePathCondition(node, false);
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
            Sequent initialConditionsSequent = createSequentForEquivalenceClassComputation(pathCondition);
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
    * <p>
    * Computes objects which should be ignored in the state because
    * they are part of the proof obligation and not of the source code.
    * </p>
    * <p>
    * By default the set will contain the exc variable and the backup
    * of arguments and the heap.
    * </p>
    * @return The objects to ignore.
    */
   protected Set<Term> computeInitialObjectsToIgnore() {
      Set<Term> result = new LinkedHashSet<Term>();
      // Add exception variable to the ignore list because it is not part of the source code.
      IProgramVariable excVar = SymbolicExecutionUtil.extractExceptionVariable(getProof());
      if (excVar instanceof ProgramVariable) {
         result.add(getServices().getTermBuilder().var((ProgramVariable)excVar));
      }
      // Add initial updates which are used as backup of the heap and method arguments. They are not part of the source code and should be ignored.
      Sequent sequent = getRoot().sequent();
      for (SequentFormula sf : sequent.succedent()) {
         Term term = sf.formula();
         if (Junctor.IMP.equals(term.op())) {
            if (term.sub(1).op() instanceof UpdateApplication) {
               Term updateApplcationTerm = term.sub(1);
               Term updateTerm = UpdateApplication.getUpdate(updateApplcationTerm);
               if (updateTerm.op() == UpdateJunctor.PARALLEL_UPDATE) {
                  for (Term subUpdate : updateTerm.subs()) {
                     if (subUpdate.op() instanceof ElementaryUpdate) {
                        ElementaryUpdate eu = (ElementaryUpdate)subUpdate.op();
                        if (eu.lhs() instanceof ProgramVariable) {
                           result.add(getServices().getTermBuilder().var((ProgramVariable)eu.lhs()));
                        }
                     }
                  }
               }
            }
         }
      }
      return result;
   }

   /**
    * Removes all conditions from the given path condition which contains
    * implicit {@link IProgramVariable}s.
    * @param pathCondition The path condition to check.
    * @return The new path condition without conditions which uses implicit {@link IProgramVariable}s.
    */
   protected Term removeImplicitSubTermsFromPathCondition(Term pathCondition) {
      if (Junctor.AND == pathCondition.op()) {
         // Path condition with multiple terms combined via AND
         List<Term> newTerms = new LinkedList<Term>();
         for (Term sub : pathCondition.subs()) {
            if (!containsImplicitProgramVariable(sub)) {
               newTerms.add(sub);
            }
         }
         return getServices().getTermBuilder().and(newTerms);
      }
      else {
         // Only one term in path condition
         if (!containsImplicitProgramVariable(pathCondition)) {
            return pathCondition;
         }
         else {
            return getServices().getTermBuilder().tt();
         }
      }
   }

   /**
    * Checks if the given {@link Term} contains an implicit {@link IProgramVariable}.
    * @param term The {@link Term} to check.
    * @return {@code true} {@link Term} contains implicit {@link IProgramVariable}, {@code false} {@link Term} contains no implicit {@link IProgramVariable}.
    */
   protected boolean containsImplicitProgramVariable(Term term) {
      if (term.op() instanceof ProgramVariable && isImplicitProgramVariable((ProgramVariable)term.op())) {
         return true;
      }
      for (int i = 0; i < term.arity(); i++) {
         if (containsImplicitProgramVariable(term.sub(i))) {
            return true;
         }
      }
      return false;
   }

   /**
    * Checks if the given {@link ProgramVariable} is implicit.
    * @param var The {@link ProgramVariable} to check.
    * @return {@code true} {@link ProgramVariable} is implicit, {@code false} {@link ProgramVariable} is not implicit or {@code null}.
    */
   protected boolean isImplicitProgramVariable(ProgramVariable var) {
      return var != null && var.isImplicit();
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
    * The created {@link Sequent} is a modified version of the {@link Sequent}
    * provided by the proofs root node. It contains the given path condition
    * as additional antecedent and the modality with the java code is removed.
    * </p>
    * @param pathCondition The path condition to include.
    * @return The created {@link Sequent} to use for equivalence class computation.
    */
   protected Sequent createSequentForEquivalenceClassComputation(Term pathCondition) {
      // Get original sequent
      Sequent originalSequent = getRoot().sequent();
      // Add path condition to antecedent
      Semisequent newAntecedent = originalSequent.antecedent();
      newAntecedent = newAntecedent.insertLast(new SequentFormula(pathCondition)).semisequent();
      // Remove everything after modality from sequent
      Semisequent newSuccedent = Semisequent.EMPTY_SEMISEQUENT;
      for (SequentFormula sf : originalSequent.succedent()) {
         Term term = sf.formula();
         if (Junctor.IMP.equals(term.op())) {
            Term newImplication = getServices().getTermBuilder().imp(term.sub(0), getServices().getTermBuilder().ff());
            newSuccedent = newSuccedent.insertLast(new SequentFormula(newImplication)).semisequent();
            // Updates are not required, because getServices().getTermBuilder().apply(updates, true) is just true
         }
         else {
            newSuccedent = newSuccedent.insertLast(sf).semisequent();
         }
      }
      return Sequent.createSequent(newAntecedent, newSuccedent);
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
      starter.start(false);
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
            starter.start(branches, false);
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
    * Computes for each location (value/association of an object) used in the 
    * given {@link Sequent} the {@link Term}s which allows to compute the object 
    * itself and the value of the value/association. The result is a {@link Set}  
    * of {@link ExtractLocationParameter} which contains the computed {@link Term}s.
    * @param sequent The {@link Sequent} to extract locations from.
    * @param objectsToIgnore The objects to ignore.
    * @return The found locations.
    * @throws ProofInputException Occurred Exception.
    */
   protected Set<ExtractLocationParameter> extractLocationsFromSequent(Sequent sequent, 
                                                                       Set<Term> objectsToIgnore) throws ProofInputException {
      Set<ExtractLocationParameter> result = new LinkedHashSet<ExtractLocationParameter>();
      for (SequentFormula sf : sequent.antecedent()) {
         result.addAll(extractLocationsFromTerm(sf.formula(), objectsToIgnore));
      }
      for (SequentFormula sf : sequent.succedent()) {
         Term term = sf.formula();
         if (Junctor.IMP != term.op()) {
            result.addAll(extractLocationsFromTerm(term, objectsToIgnore));
         }
      }
      return result;
   }
   
   /**
    * Computes for each location (value/association of an object) used in the 
    * given {@link Term} the {@link Term}s which allows to compute the object 
    * itself and the value of the value/association. The result is a {@link Set}  
    * of {@link ExtractLocationParameter} which contains the computed {@link Term}s.
    * @param term The {@link Term} to extract locations from.
    * @param objectsToIgnore The objects to ignore.
    * @return The found locations.
    * @throws ProofInputException Occurred Exception.
    */
   protected Set<ExtractLocationParameter> extractLocationsFromTerm(Term term, 
                                                                    Set<Term> objectsToIgnore) throws ProofInputException {
      Set<ExtractLocationParameter> result = new LinkedHashSet<ExtractLocationParameter>();
      collectLocationsFromTerm(result, term, objectsToIgnore);
      return result;
   }
   
   /**
    * Utility method of {@link #extractLocationsFromTerm(Term, Set)} which
    * recursively extracts the locations.
    * @param toFill The result {@link Set} to fill.
    * @param term The current {@link Term}.
    * @param objectsToIgnore The objects to ignore.
    * @throws ProofInputException Occurred Exception.
    */
   protected void collectLocationsFromTerm(Set<ExtractLocationParameter> toFill, Term term, Set<Term> objectsToIgnore) throws ProofInputException {
      final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
      if (term.op() instanceof ProgramVariable) {
         ProgramVariable var = (ProgramVariable)term.op();
         if (!SymbolicExecutionUtil.isHeap(var, heapLDT) && 
             !isImplicitProgramVariable(var) && 
             !objectsToIgnore.contains(term)) {
            toFill.add(new ExtractLocationParameter(var, true));
         }
      }
      else {
         Sort sort = heapLDT.getSortOfSelect(term.op());
         if (sort != null) {
            Term selectTerm = term.sub(1);
            if (!objectsToIgnore.contains(selectTerm) &&
                !SymbolicExecutionUtil.isSkolemConstant(selectTerm)) {
               ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, term.sub(2));
               if (var != null) {
                  if (!isImplicitProgramVariable(var)) {
                     if (var.isStatic()) {
                        toFill.add(new ExtractLocationParameter(var, true));
                     }
                     else {
                        if (selectTerm.op() instanceof ProgramVariable) {
                           toFill.add(new ExtractLocationParameter((ProgramVariable)selectTerm.op(), true));
                        }
                        toFill.add(new ExtractLocationParameter(var, selectTerm));
                     }
                  }
               }
               else {
                  int arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, term.sub(2));
                  if (arrayIndex >= 0) {
                     if (selectTerm.op() instanceof ProgramVariable) {
                        toFill.add(new ExtractLocationParameter((ProgramVariable)selectTerm.op(), true));
                     }
                     toFill.add(new ExtractLocationParameter(arrayIndex, selectTerm));
                  }
                  else {
                     throw new ProofInputException("Unsupported select statement \"" + term + "\".");
                  }
               }
            }
         }
         else if (heapLDT.getLength() == term.op()) {
            if (!objectsToIgnore.contains(term.sub(0))) {
               ProgramVariable var = getServices().getJavaInfo().getArrayLength();
               toFill.add(new ExtractLocationParameter(var, term.sub(0)));
            }
         }
         else {
            for (Term sub : term.subs()) {
               collectLocationsFromTerm(toFill, sub, objectsToIgnore);
            }
         }
      }
   }

   /**
    * <p>
    * Computes for each location (value/association of an object) used in the 
    * updates of the given {@link Sequent} the {@link Term}s which allows to compute the object 
    * itself and the value of the value/association. The result is a {@link Set}  
    * of {@link ExtractLocationParameter} which contains the computed {@link Term}s.
    * </p>
    * <p>
    * Objects which are created in the heap during symbolic execution and
    * all objects which are used on the right side of associations are also 
    * collected and stored in the {@link Set}s {@code updateCreatedObjectsToFill}/
    * {@code updateValueObjectsToFill}.
    * </p>
    * @param sequent The {@link Sequent} which provides the updates to extract locations from.
    * @param locationsToFill The location {@link Set} to fill.
    * @param updateCreatedObjectsToFill The new created object {@link Set} to fill.
    * @param updateValueObjectsToFill The {@link Set} with objects used on right side of updates to fill.
    * @param objectsToIgnore The objects to ignore.
    * @throws ProofInputException Occurred Exception.
    */
   protected void collectLocationsFromUpdates(Sequent sequent, 
                                              Set<ExtractLocationParameter> locationsToFill, 
                                              Set<Term> updateCreatedObjectsToFill, 
                                              Set<Term> updateValueObjectsToFill, 
                                              Set<Term> objectsToIgnore) throws ProofInputException {
      Term updateApplication = findUpdates(sequent);
      if (updateApplication == null) {
         throw new ProofInputException("Can't find update application in \"" + sequent + "\".");
      }
      Term topUpdate = UpdateApplication.getUpdate(updateApplication);
      collectLocationsFromTerm(topUpdate, locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill, objectsToIgnore);
   }
   
   /**
    * Searches the {@link Term} with the updates in the given {@link Sequent}.
    * @param sequent The {@link Sequent} to search update {@link Term} in.
    * @return The found {@link Term} with the {@link UpdateApplication} or {@code null} if not found.
    */
   protected Term findUpdates(Sequent sequent) {
      Term result = null;
      Iterator<SequentFormula> sucIter = sequent.succedent().iterator();
      while (result == null && sucIter.hasNext()) {
         SequentFormula sf = sucIter.next();
         Term term = sf.formula();
         if (UpdateApplication.UPDATE_APPLICATION == term.op()) {
            result = term;
         }
      }
      return result;
   }

   /**
    * <p>
    * Computes for each location (value/association of an object) used in the 
    * the given {@link Term} the {@link Term}s which allows to compute the object 
    * itself and the value of the value/association. The result is a {@link Set}  
    * of {@link ExtractLocationParameter} which contains the computed {@link Term}s.
    * </p>
    * <p>
    * Objects which are created in the heap during symbolic execution and
    * all objects which are used on the right side of associations are also 
    * collected and stored in the {@link Set}s {@code updateCreatedObjectsToFill}/
    * {@code updateValueObjectsToFill}.
    * </p>
    * @param updateTerm The {@link Term} which provides the update to extract locations from.
    * @param locationsToFill The location {@link Set} to fill.
    * @param updateCreatedObjectsToFill The new created object {@link Set} to fill.
    * @param updateValueObjectsToFill The {@link Set} with objects used on right side of updates to fill.
    * @param objectsToIgnore The objects to ignore.
    * @throws ProofInputException Occurred Exception.
    */
   protected void collectLocationsFromTerm(Term updateTerm, 
                                           Set<ExtractLocationParameter> locationsToFill, 
                                           Set<Term> updateCreatedObjectsToFill, 
                                           Set<Term> updateValueObjectsToFill,
                                           Set<Term> objectsToIgnore) throws ProofInputException {
      if (updateTerm.op() instanceof UpdateJunctor) {
         for (Term sub : updateTerm.subs()) {
            collectLocationsFromTerm(sub, locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill, objectsToIgnore);
         }
      }
      else if (updateTerm.op() instanceof ElementaryUpdate) {
         ElementaryUpdate eu = (ElementaryUpdate)updateTerm.op();
         if (SymbolicExecutionUtil.isHeapUpdate(getServices(), updateTerm)) {
            collectLocationsFromHeapUpdate(updateTerm.sub(0), locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
         }
         else if (eu.lhs() instanceof ProgramVariable) {
            final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
            ProgramVariable var = (ProgramVariable)eu.lhs();
            if (!SymbolicExecutionUtil.isHeap(var, heapLDT)) {
               if (!isImplicitProgramVariable(var) && !objectsToIgnore.contains(getServices().getTermBuilder().var(var))) {
                  locationsToFill.add(new ExtractLocationParameter(var, true));
               }
               if (SymbolicExecutionUtil.hasReferenceSort(getServices(), updateTerm.sub(0))) {
                  Term objectTerm = updateTerm.sub(0);
                  objectTerm = SymbolicExecutionUtil.replaceSkolemConstants(node.sequent(), objectTerm, getServices());
                  updateValueObjectsToFill.add(objectTerm);
               }
            }
         }
         else {
            throw new ProofInputException("Unsupported update operator \"" + eu.lhs() + "\".");
         }
      }
      else {
         throw new ProofInputException("Unsupported update operator \"" + updateTerm.op() + "\".");
      }
   }
   
   /**
    * <p>
    * Computes for each location (value/association of an object) used in the 
    * the given heap update {@link Term} the {@link Term}s which allows to compute the object 
    * itself and the value of the value/association. The result is a {@link Set}  
    * of {@link ExtractLocationParameter} which contains the computed {@link Term}s.
    * </p>
    * <p>
    * Objects which are created in the heap during symbolic execution and
    * all objects which are used on the right side of associations are also 
    * collected and stored in the {@link Set}s {@code updateCreatedObjectsToFill}/
    * {@code updateValueObjectsToFill}.
    * </p>
    * @param term The {@link Term} which provides the heap update to extract locations from.
    * @param locationsToFill The location {@link Set} to fill.
    * @param updateCreatedObjectsToFill The new created object {@link Set} to fill.
    * @param updateValueObjectsToFill The {@link Set} with objects used on right side of updates to fill.
    * @throws ProofInputException Occurred Exception.
    */
   protected void collectLocationsFromHeapUpdate(Term term,
                                                 Set<ExtractLocationParameter> locationsToFill, 
                                                 Set<Term> updateCreatedObjectsToFill, 
                                                 Set<Term> updateValueObjectsToFill) throws ProofInputException {
      final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
      if (term.op() == heapLDT.getStore()) {
         // Add select object term to result
         Term selectArgument = term.sub(1);
         if (heapLDT.getSortOfSelect(selectArgument.op()) != null) {
            ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, selectArgument.sub(2));
            if (var != null) {
               if (!isImplicitProgramVariable(var)) {
                  locationsToFill.add(new ExtractLocationParameter(var, selectArgument.sub(1)));
               }
            }
            else {
               int arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, selectArgument.sub(2));
               if (arrayIndex >= 0) {
                  locationsToFill.add(new ExtractLocationParameter(arrayIndex, selectArgument.sub(1)));
               }
               else {
                  throw new ProofInputException("Unsupported select statement \"" + term + "\".");
               }
            }
         }
         else if (selectArgument.op() instanceof IProgramVariable) {
            ProgramVariable var = (ProgramVariable)selectArgument.op();
            if (!isImplicitProgramVariable(var)) {
               locationsToFill.add(new ExtractLocationParameter(var, false));
            }
         }
         else if (heapLDT.getNull() == selectArgument.op()) {
            // Static fields have a null term as select argument.
         }
         else {
            for (int i = 0; i < selectArgument.arity(); i++) {
               collectLocationsFromHeapUpdate(selectArgument.sub(i), locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
            }
         }
         // Add select value term to result
         ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, term.sub(2));
         if (var != null) {
            if (!isImplicitProgramVariable(var)) {
               if (var.isStatic()) {
                  locationsToFill.add(new ExtractLocationParameter(var, true));
               }
               else {
                  locationsToFill.add(new ExtractLocationParameter(var, term.sub(1)));
               }
            }
         }
         else {
            int arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, term.sub(2));
            if (arrayIndex >= 0) {
               locationsToFill.add(new ExtractLocationParameter(arrayIndex, term.sub(1)));
            }
            else {
               throw new ProofInputException("Unsupported select statement \"" + term + "\".");
            }
         }
         if (SymbolicExecutionUtil.hasReferenceSort(getServices(), term.sub(3)) && term.sub(3).op() instanceof ProgramVariable) {
            Term objectTerm = term.sub(3);
            objectTerm = SymbolicExecutionUtil.replaceSkolemConstants(node.sequent(), objectTerm, getServices());
            updateValueObjectsToFill.add(objectTerm);
         }
         // Iterate over child heap modifications
         collectLocationsFromHeapUpdate(term.sub(0), locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
      }
      else if (term.op() == heapLDT.getCreate()) {
         Term newObject = term.sub(1);
         newObject = SymbolicExecutionUtil.replaceSkolemConstants(node.sequent(), newObject, getServices());
         updateCreatedObjectsToFill.add(newObject);
         // Iterate over child heap modifications
         collectLocationsFromHeapUpdate(term.sub(0), locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
      }
      else if (term.op() == heapLDT.getHeap()) {
         // Initial Heap, nothing to do
      }
      else if (term.op() == heapLDT.getMemset()) {
         // Array initialization, nothing to do.
         // Iterate over child heap modifications
         collectLocationsFromHeapUpdate(term.sub(0), locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
      }
      else {
         for (int i = 0; i < term.arity(); i++) {
            collectLocationsFromHeapUpdate(term.sub(i), locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
         }
      }
   }

   /**
    * Creates a predicate and a {@link Term} which can be used to compute the 
    * values defined by the given {@link ExtractLocationParameter}s.
    * @param valueSelectParameter The {@link ExtractLocationParameter}s to compute in the created {@link Term}.
    * @return The created {@link Term} which computes the values of the given {@link ExtractLocationParameter}s.
    */
   protected Term createLocationPredicateAndTerm(Set<ExtractLocationParameter> valueSelectParameter) {
      List<Term> argumentsList = new LinkedList<Term>();
      int argumentIndex = -1;
      for (ExtractLocationParameter param : valueSelectParameter) {
         argumentsList.add(param.createPreParentTerm());
         param.setParentTermIndexInStatePredicate(++argumentIndex);
         argumentsList.add(param.createPreValueTerm());
         param.setValueTermIndexInStatePredicate(++argumentIndex);
      }
      Term[] arguments = argumentsList.toArray(new Term[argumentsList.size()]);
      Sort[] sorts = new Sort[arguments.length];
      for (int i = 0; i < sorts.length; i++) {
         sorts[i] = arguments[i].sort();
      }
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(getServices().getTermBuilder().newName("LayoutPredicate")), Sort.FORMULA, sorts);
      // Create formula which contains the value interested in.
      Term newTerm = getServices().getTermBuilder().func(newPredicate, arguments);
      return newTerm;
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
      return getLayout(getRoot(), initialLayouts, layoutIndex, initialLocationTerm, initialLocations, pathCondition, computeInitialStateName());
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
      return getLayout(node, currentLayouts, layoutIndex, currentLocationTerm, currentLocations, pathCondition, computeCurrentStateName());
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
    * @param node The {@link Node} which provides the state.
    * @param confiurationsMap The map which contains already computed memory layouts.
    * @param layoutIndex The index of the memory layout to lazily compute and return.
    * @param layoutTerm The result term to use in side proof.
    * @param locations The locations to compute in side proof.
    * @param pathCondition An optional path condition to include in the side proof.
    * @param stateName The name of the state.
    * @return The lazily computed memory layout.
    * @throws ProofInputException Occurred Exception.
    */
   protected ISymbolicLayout getLayout(Node node,
                                              Map<Integer, ISymbolicLayout> confiurationsMap, 
                                              int layoutIndex,
                                              Term layoutTerm,
                                              Set<ExtractLocationParameter> locations,
                                              Term pathCondition,
                                              String stateName) throws ProofInputException {
      synchronized (this) {
         assert layoutIndex >= 0;
         assert layoutIndex < appliedCutsPerLayout.size();
         assert isAnalysed();
         ISymbolicLayout result = confiurationsMap.get(Integer.valueOf(layoutIndex));
         if (result == null) {
            // Get memory layout
            ImmutableSet<Term> layout = appliedCutsPerLayout.get(layoutIndex);
            ImmutableList<ISymbolicEquivalenceClass> equivalentClasses = getEquivalenceClasses(layoutIndex);
            result = lazyComputeLayout(node, layout, layoutTerm, locations, equivalentClasses, pathCondition, stateName);
            confiurationsMap.put(Integer.valueOf(layoutIndex), result);
         }
         return result;
      }
   }
   
   /**
    * <p>
    * Computes a memory layout lazily when it is first time requested via 
    * {@link #getLayout(Node, Map, int, Term, Set, Term, String)}.
    * </p>
    * <p>
    * The method starts a side proof with the given arguments to compute
    * the values and objects of the requested memory layout. The
    * {@link ExecutionVariableValuePair} together with the memory layout term
    * defines how to access the side proof result.
    * </p>
    * <p>
    * The next step is the result extraction from side proof which results
    * in a {@link Set} of {@link ExecutionVariableValuePair} instances. Each
    * instance defines a value or association of a parent object or the state itself.
    * </p>
    * <p>
    * Finally, the last step is to create the {@link ISymbolicLayout} instance
    * and to fill it with the values/associations defined by {@link ExecutionVariableValuePair} instances.
    * </p>
    * @param node The {@link Node} which provides the state.
    * @param layout The memory layout terms.
    * @param layoutTerm The result term to use in side proof.
    * @param locations The locations to compute in side proof.
    * @param equivalentClasses The equivalence classes defined by the memory layout terms.
    * @param pathCondition An optional path condition to include in the side proof.
    * @param stateName The name of the state.
    * @return The created memory layout.
    * @throws ProofInputException Occurred Exception.
    */
   protected ISymbolicLayout lazyComputeLayout(Node node,
                                               ImmutableSet<Term> layout, 
                                               Term layoutTerm,
                                               Set<ExtractLocationParameter> locations,
                                               ImmutableList<ISymbolicEquivalenceClass> equivalentClasses,
                                               Term pathCondition,
                                               String stateName) throws ProofInputException {
      if (!locations.isEmpty()) {
         // Get original updates
         Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
         ImmutableList<Term> originalUpdates = TermBuilder.goBelowUpdates2(originalModifiedFormula).first;
         // Combine memory layout with original updates
         Term layoutCondition = getServices().getTermBuilder().and(layout);
         if (pathCondition != null) {
            layoutCondition = getServices().getTermBuilder().and(layoutCondition, pathCondition);
         }
         ImmutableList<Term> additionalUpdates = ImmutableSLList.nil();
         for (Term originalUpdate : originalUpdates) {
            if (UpdateJunctor.PARALLEL_UPDATE == originalUpdate.op()) {
               additionalUpdates = additionalUpdates.append(originalUpdate.subs());
            }
            else if (originalUpdate.op() instanceof ElementaryUpdate) {
               additionalUpdates = additionalUpdates.append(originalUpdate);
            }
            else {
               throw new ProofInputException("Unexpected update operator \"" + originalUpdate.op() + "\".");
            }
         }
         for (ExtractLocationParameter evp : locations) {
            additionalUpdates = additionalUpdates.append(evp.createPreUpdate());
         }
         ImmutableList<Term> newUpdates = ImmutableSLList.<Term>nil().append(getServices().getTermBuilder().parallel(additionalUpdates));
         Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, layoutCondition, layoutTerm, newUpdates, false);
         // Instantiate and run proof
         ApplyStrategy.ApplyStrategyInfo info = SideProofUtil.startSideProof(getProof(), 
                                                                             sequent, 
                                                                             StrategyProperties.METHOD_CONTRACT,
                                                                             StrategyProperties.LOOP_INVARIANT,
                                                                             StrategyProperties.QUERY_ON,
                                                                             StrategyProperties.SPLITTING_NORMAL,
                                                                             true);
         try {
            // Extract values and objects from result predicate and store them in variable value pairs
            Set<ExecutionVariableValuePair> pairs = new LinkedHashSet<ExecutionVariableValuePair>();
            int goalCount = info.getProof().openGoals().size();
            for (Goal goal : info.getProof().openGoals()) {
               Term resultTerm = SideProofUtil.extractOperatorTerm(goal, layoutTerm.op());
               Term condition = goalCount == 1 ? null : SymbolicExecutionUtil.computePathCondition(goal.node(), true);
               for (ExtractLocationParameter param : locations) {
                  ExecutionVariableValuePair pair;
                  if (param.isArrayIndex()) {
                     pair = new ExecutionVariableValuePair(param.getArrayIndex(), param.getParentTerm(), resultTerm.sub(param.getValueTermIndexInStatePredicate()), condition, param.isStateMember());
                  }
                  else {
                     pair = new ExecutionVariableValuePair(param.getProgramVariable(), param.getParentTerm(), resultTerm.sub(param.getValueTermIndexInStatePredicate()), condition, param.isStateMember());
                  }
                  pairs.add(pair);
               }
            }
            // Create memory layout
            return createLayoutFromExecutionVariableValuePairs(equivalentClasses, pairs, stateName);
         }
         finally {
            SideProofUtil.disposeOrStore("Layout computation on node " + node.serialNr() + " with layout term " + ProofSaver.printAnything(layoutTerm, getServices()) + ".", info);
         }
      }
      else {
         // Create empty memory layout
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

   /**
    * Returns the {@link Proof} of the analyzed {@link Node}.
    * @return The {@link Proof} of the analyzed {@link Node}.
    */
   protected Proof getProof() {
      return node.proof();
   }
   
   /**
    * Returns the root {@link Node} of the proof.
    * @return The root {@link Node} of the proof.
    */
   protected Node getRoot() {
      return getProof().root();
   }
   
   /**
    * Returns the {@link Services} of the analyzed {@link Node}.
    * @return The {@link Services} of the analyzed {@link Node}.
    */
   protected Services getServices() {
      return getProof().getServices();
   }

   /**
    * Creates a new {@link LocationVariable} with the given name and {@link Sort}.
    * @param name The name of the new variable.
    * @param sort The {@link Sort} of the new variable.
    * @return The created {@link LocationVariable}.
    * @throws ProofInputException Occurred Exception.
    */
   protected LocationVariable createLocationVariable(String name, Sort sort) throws ProofInputException {
      final KeYJavaType kjt = getServices().getJavaInfo().getKeYJavaType(sort);
      if (kjt == null) {
         throw new ProofInputException("Can't find Java type of sort \"" + sort + "\".");
      }
      return new LocationVariable(new ProgramElementName(name), kjt);
   }

   /**
    * <p>
    * Instances of this class provides the {@link Term} which are required
    * to compute a location (value or association of a given object/state).
    * </p>
    * <p>
    * Instances of this class can be used to compute the values in each memory layout.
    * So they are instantiated during the analyzation phase 
    * {@link SymbolicLayoutExtractor#analyse()} once for initial and current memory layout.
    * </p>
    * @author Martin Hentschel
    */
   protected class ExtractLocationParameter {
      /**
       * The {@link ProgramVariable} or {@code null} if an array index is used instead.
       */
      private ProgramVariable programVariable;
      
      /**
       * The array index or {@code -1} if a {@link ProgramVariable} is used instead.
       */
      private int arrayIndex;
      
      /**
       * An optional parent object represented as {@link Term}. If it is {@code null} an {@link IProgramVariable} of the state is represented.
       */
      private Term parentTerm;
      
      /**
       * The index of the parent argument in the predicate used in side proof to compute the values.
       */
      private int parentTermIndexInStatePredicate;

      /**
       * The index of the value argument in the predicate used in side proof to compute the values.
       */
      private int valueTermIndexInStatePredicate;

      /**
       * The {@link LocationVariable} which is used to make sure that the defined parent object
       * of the initial state is used, because the expression (e.g. {@code x.next}) might refer
       * to different objects in the current state.
       */
      private LocationVariable preVariable;
      
      /**
       * Defines if this location should explicitly be shown on the state.
       */
      private boolean stateMember;

      /**
       * Constructor.
       * @param programVariable The {@link ProgramVariable}.
       * @param stateMember Defines if this location should explicitly be shown on the state.
       * @throws ProofInputException Occurred Exception.
       */
      public ExtractLocationParameter(ProgramVariable programVariable, 
                                      boolean stateMember) throws ProofInputException {
         this(programVariable, null);
         this.stateMember = stateMember;
      }

      /**
       * Constructor.
       * @param programVariable The {@link ProgramVariable}.
       * @param parentTerm The parent object represented as {@link Term}.
       * @throws ProofInputException Occurred Exception.
       */
      public ExtractLocationParameter(ProgramVariable programVariable, 
                                      Term parentTerm) throws ProofInputException {
         assert programVariable != null;
         this.programVariable = programVariable;
         this.parentTerm = parentTerm;
         this.preVariable = createLocationVariable("Pre" + preVariableIndex++, parentTerm != null ? parentTerm.sort() : programVariable.sort());
         this.arrayIndex = -1;
      }
      
      /**
       * Constructor.
       * @param arrayIndex The array index.
       * @param parentTerm The parent object represented as {@link Term}.
       * @throws ProofInputException Occurred Exception.
       */
      public ExtractLocationParameter(int arrayIndex, 
                                      Term parentTerm) throws ProofInputException {
         assert parentTerm != null;
         this.arrayIndex = arrayIndex;
         this.parentTerm = parentTerm;
         this.preVariable = createLocationVariable("Pre" + preVariableIndex++, parentTerm.sort());
      }

      /**
       * Checks if this location should explicitly be shown on the state.
       * @return Show location on state?
       */
      public boolean isStateMember() {
         return stateMember;
      }

      /**
       * Checks if an array index or a {@link ProgramVariable} is represented.
       * @return {@code true} is array index, {@code false} is {@link ProgramVariable}. 
       */
      public boolean isArrayIndex() {
         return arrayIndex >= 0;
      }
      
      /**
       * Returns the array index.
       * @return The array index.
       */
      public int getArrayIndex() {
         return arrayIndex;
      }

      /**
       * Creates the pre update to make sure that the parent object defined
       * by the expression is evaluated on the initial state because it might
       * be changed in the current state due to updates.
       * @return The created {@link Term} with the pre update.
       */
      public Term createPreUpdate() {
         Term originalTerm = parentTerm != null ? parentTerm : getServices().getTermBuilder().var(programVariable);
         return getServices().getTermBuilder().elementary(preVariable, originalTerm);
      }
      
      /**
       * Creates the {@link Term} to compute the parent object with help of the pre update.
       * @return The {@link Term} to compute the parent object with help of the pre update.
       */
      public Term createPreParentTerm() {
         return getServices().getTermBuilder().var(preVariable);
      }
      
      /**
       * Computes the {@link Term} to compute the value with help of the pre update.
       * @return The {@link Term} to compute the value with help of the pre update.
       */
      public Term createPreValueTerm() {
         if (parentTerm != null) {
            if (isArrayIndex()) {
               Term idx = getServices().getTermBuilder().zTerm("" + arrayIndex);
               return getServices().getTermBuilder().dotArr(parentTerm, idx);
            }
            else {
               if (getServices().getJavaInfo().getArrayLength() == programVariable) {
                  // Special handling for length attribute of arrays
                  Function function = getServices().getTypeConverter().getHeapLDT().getLength();
                  return getServices().getTermBuilder().func(function, createPreParentTerm());
               }
               else {
                  Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)programVariable, getServices());
                  return getServices().getTermBuilder().dot(programVariable.sort(), createPreParentTerm(), function);
               }
            }
         }
         else {
            if (programVariable.isStatic()) {
               Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)programVariable, getServices());
               return getServices().getTermBuilder().staticDot(programVariable.sort(), function);
            }
            else {
               return getServices().getTermBuilder().var(programVariable);
            }
         }
      }

      /**
       * Returns the {@link ProgramVariable} or {@code null} if an array index is used instead.
       * @return The {@link ProgramVariable} or {@code null} if an array index is used instead.
       */
      public ProgramVariable getProgramVariable() {
         return programVariable;
      }

      /**
       * Returns the optional parent object represented as {@link Term}. If it is {@code null} an {@link IProgramVariable} of the state is represented.
       * @return The optional parent object represented as {@link Term}. If it is {@code null} an {@link IProgramVariable} of the state is represented.
       */
      public Term getParentTerm() {
         return parentTerm;
      }

      /**
       * Returns the index of the parent argument in the predicate used in side proof to compute the values.
       * @return The index of the parent argument in the predicate used in side proof to compute the values.
       */
      public int getParentTermIndexInStatePredicate() {
         return parentTermIndexInStatePredicate;
      }

      /**
       * Sets the index of the parent argument in the predicate used in side proof to compute the values.
       * @param selectParentTermIndexInStatePredicate The index of the parent argument in the predicate used in side proof to compute the values.
       */
      public void setParentTermIndexInStatePredicate(int selectParentTermIndexInStatePredicate) {
         this.parentTermIndexInStatePredicate = selectParentTermIndexInStatePredicate;
      }

      /**
       * Returns the index of the value argument in the predicate used in side proof to compute the values.
       * @return The index of the value argument in the predicate used in side proof to compute the values.
       */
      public int getValueTermIndexInStatePredicate() {
         return valueTermIndexInStatePredicate;
      }

      /**
       * Sets the index of the value argument in the predicate used in side proof to compute the values.
       * @param selectValueTermIndexInStatePredicate The index of the value argument in the predicate used in side proof to compute the values.
       */
      public void setValueTermIndexInStatePredicate(int selectValueTermIndexInStatePredicate) {
         this.valueTermIndexInStatePredicate = selectValueTermIndexInStatePredicate;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         if (isArrayIndex()) {
            return "[" + arrayIndex + "] " + (parentTerm != null ? " of " + parentTerm : "");
         }
         else {
            return programVariable + (parentTerm != null ? " of " + parentTerm : "");
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj instanceof ExtractLocationParameter) {
            ExtractLocationParameter other = (ExtractLocationParameter)obj;
            return arrayIndex == other.arrayIndex &&
                   stateMember == other.stateMember &&
                   JavaUtil.equals(parentTerm, other.parentTerm) &&
                   JavaUtil.equals(programVariable, other.programVariable);
         }
         else {
            return false;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int hashCode() {
         int result = 17;
         result = 31 * result + arrayIndex;
         result = 31 * result + (stateMember ? 1 : 0);
         result = 31 * result + (parentTerm != null ? parentTerm.hashCode() : 0);
         result = 31 * result + (programVariable != null ? programVariable.hashCode() : 0);
         return result;
      }
   }
   
   /**
    * <p>
    * Represents a location (value or association of a given object/state) 
    * in a concrete memory layout of the initial or current state.
    * </p>
    * <p>
    * They are instantiated lazily when a concrete memory layout is requested
    * the first during lazily computation 
    * {@link SymbolicLayoutExtractor#lazyComputeLayout(Node, ImmutableSet, Term, Set, ImmutableList, Term, String)}.
    * The instances exists only temporary until the concrete {@link ISymbolicLayout} was created from them.
    * </p>
    * @author Martin Hentschel
    */
   protected static class ExecutionVariableValuePair {
      /**
       * The {@link ProgramVariable} or {@code null} if an array index is used instead.
       */
      private ProgramVariable programVariable;

      /**
       * The array index or {@code -1} if a {@link ProgramVariable} is used instead.
       */
      private int arrayIndex;
      
      /**
       * An optional parent object or {@code null} if it is a value/association of the state.
       */
      private Term parent;
      
      /**
       * The value or association target.
       */
      private Term value;
      
      /**
       * Defines if this location should explicitly be shown on the state.
       */
      private boolean stateMember;
      
      /**
       * An optional condition under which the value is valid.
       */
      private Term condition;

      /**
       * Constructor.
       * @param programVariable The {@link ProgramVariable}.
       * @param parent An optional parent object or {@code null} if it is a value/association of the state.
       * @param value The value or association target.
       * @param condition An optional condition under which the value is valid.
       * @param stateMember Defines if this location should explicitly be shown on the state.
       */
      public ExecutionVariableValuePair(ProgramVariable programVariable, 
                                        Term parent, 
                                        Term value, 
                                        Term condition,
                                        boolean stateMember) {
         assert programVariable != null;
         assert value != null;
         this.programVariable = programVariable;
         this.parent = parent;
         this.value = value;
         this.condition = condition;
         this.arrayIndex = -1;
         this.stateMember = stateMember;
      }

      /**
       * Constructor.
       * @param arrayIndex The array index.
       * @param parent The parent object.
       * @param value The value or association target.
       * @param condition An optional condition under which the value is valid.
       * @param stateMember Defines if this location should explicitly be shown on the state.
       */
      public ExecutionVariableValuePair(int arrayIndex, 
                                        Term parent, 
                                        Term value, 
                                        Term condition,
                                        boolean stateMember) {
         assert parent != null;
         assert value != null;
         this.arrayIndex = arrayIndex;
         this.parent = parent;
         this.value = value;
         this.condition = condition;
         this.stateMember = stateMember;
      }

      /**
       * Returns the {@link ProgramVariable} or {@code null} if an array index is used instead.
       * @return The {@link ProgramVariable} or {@code null} if an array index is used instead.
       */
      public ProgramVariable getProgramVariable() {
         return programVariable;
      }

      /**
       * Returns the optional parent object or {@code null} if it is a value/association of the state.
       * @return The optional parent object or {@code null} if it is a value/association of the state.
       */
      public Term getParent() {
         return parent;
      }

      /**
       * Returns the value or association target.
       * @return The value or association target.
       */
      public Term getValue() {
         return value;
      }
      
      /**
       * Checks if an array index or a {@link ProgramVariable} is represented.
       * @return {@code true} is array index, {@code false} is {@link ProgramVariable}. 
       */
      public boolean isArrayIndex() {
         return arrayIndex >= 0;
      }

      /**
       * Returns the array index.
       * @return The array index.
       */
      public int getArrayIndex() {
         return arrayIndex;
      }

      /**
       * Checks if this location should explicitly be shown on the state.
       * @return Show location on state?
       */
      public boolean isStateMember() {
         return stateMember;
      }

      /**
       * Returns the optional condition under which the value is valid.
       * @return The optional condition under which the value is valid.
       */
      public Term getCondition() {
         return condition;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean equals(Object obj) {
         if (obj instanceof ExecutionVariableValuePair) {
            ExecutionVariableValuePair other = (ExecutionVariableValuePair)obj;
            return isArrayIndex() ? getArrayIndex() == other.getArrayIndex() : getProgramVariable().equals(other.getProgramVariable()) &&
                   getParent() != null ? getParent().equals(other.getParent()) : other.getParent() == null &&
                   getCondition() != null ? getCondition().equals(other.getCondition()) : other.getCondition() == null &&
                   getValue().equals(other.getValue());
         }
         else {
            return false;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int hashCode() {
         int result = 17;
         result = 31 * result + (isArrayIndex() ? getArrayIndex() : getProgramVariable().hashCode());
         result = 31 * result + (getParent() != null ? getParent().hashCode() : 0);
         result = 31 * result + (getCondition() != null ? getCondition().hashCode() : 0);
         result = 31 * result + getValue().hashCode();
         return result;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         if (isArrayIndex()) {
            return "[" + getArrayIndex() + "]" +
                   (getParent() != null ? " of " + getParent() : "") +
                   " is " + getValue();
         }
         else {
            return getProgramVariable() +
                   (getParent() != null ? " of " + getParent() : "") +
                   " is " + getValue();
         }
      }
   }
}