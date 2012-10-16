package de.uka.ilkd.key.symbolic_execution;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
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
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Visitor;
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
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicConfiguration;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.AbstractSymbolicAssociationValueContainer;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicConfiguration;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicEquivalenceClass;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicObject;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicState;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.ProofStarter;

// TODO: Implement write access of array indices
// TODO: Test array creation
// TODO: Test self references of different classes
public class SymbolicConfigurationExtractor {
   private Node node;
   
   private List<ImmutableSet<Term>> configurations;
   
   private Map<Integer, ISymbolicConfiguration> currentConfigurations;
   
   private Set<ExtractValueParameter> currentLocations;
   
   private Term currentConfigurationTerm;
   
   private Map<Integer, ISymbolicConfiguration> initialConfigurations;
   
   private Set<ExtractValueParameter> initialLocations;
   
   private Term initialConfigurationTerm;
   
   private Map<Integer, ImmutableList<ISymbolicEquivalenceClass>> configurationsEquivalentClasses;
   
   private int preVariableIndex = 0;
   
   private Term pathCondition;
   
   private Set<Term> objectsAndLocationsToIgnore;
   
   public SymbolicConfigurationExtractor(Node node) {
      assert node != null;
      this.node = node;
   }

   public void analyse() throws ProofInputException {
      synchronized (this) {
         if (!isAnalysed()) {
            // Get path condition
            pathCondition = SymbolicExecutionUtil.computePathCondition(node, true);
            pathCondition = removeImplicitSubTermsFromPathCondition(pathCondition);
            // Compute all locations used in path conditions and updates.
            Set<ExtractValueParameter> temporaryCurrentLocations = new LinkedHashSet<ExtractValueParameter>();
            objectsAndLocationsToIgnore = computeInitialLocationsToIgnore(); // Contains all objects which should be ignored, like exc of the proof obligation and created objects during symbolic execution
            Set<Term> updateValueObjects = new LinkedHashSet<Term>(); // Contains all objects which are the value of an update
            collectLocationsFromUpdates(node.sequent(), temporaryCurrentLocations, objectsAndLocationsToIgnore, updateValueObjects);
            initialLocations = termToLocations(pathCondition, objectsAndLocationsToIgnore);
            initialLocations.addAll(sequentToLocations(node.sequent(), objectsAndLocationsToIgnore));
            currentLocations = new LinkedHashSet<ExtractValueParameter>(initialLocations);
            currentLocations.addAll(temporaryCurrentLocations);
            // Compute objects for equivalence check from path condition
            Set<Term> symbolicObjectsResultingInCurrentState = collectSymbolicObjectsFromTerm(pathCondition, objectsAndLocationsToIgnore);
            symbolicObjectsResultingInCurrentState.addAll(filterOutNewupdateCreatedObjects(updateValueObjects, objectsAndLocationsToIgnore));
            symbolicObjectsResultingInCurrentState.addAll(collectSymbolicObjectsFromConditionsInSequent(node.sequent(), objectsAndLocationsToIgnore));
            symbolicObjectsResultingInCurrentState.add(TermBuilder.DF.NULL(getServices())); // Add null because it can happen that a object is null and this option must be included in equivalence class computation
            // Compute a sequent with the initial conditions of the proof without modality
            Sequent initialConditionsSequent = computeInitialConditionsSequent(pathCondition);
            // Instantiate proof in which equivalent classes of symbolic objects in path conditions are computed
            ProofStarter equivalentClassesProofStarter = SymbolicExecutionUtil.createSideProof(getProof(), initialConditionsSequent);
            // Apply cut rules to compute equivalent classes
            applyCutRules(equivalentClassesProofStarter, symbolicObjectsResultingInCurrentState);
            // Finish proof automatically
            SymbolicExecutionUtil.startSideProof(getProof(), equivalentClassesProofStarter, StrategyProperties.SPLITTING_NORMAL);
            // Compute the available instance configurations via the opened goals of the equivalent proof.
            configurations = computeInstanceConfigurationsFromGoals(equivalentClassesProofStarter.getProof());
            // Create predicate required for state computation
            initialConfigurationTerm = createConfigurationPredicateAndTerm(initialLocations);
            currentConfigurationTerm = createConfigurationPredicateAndTerm(currentLocations);
            // Create configuration maps which are filled lazily
            initialConfigurations = new HashMap<Integer, ISymbolicConfiguration>(configurations.size());
            currentConfigurations = new HashMap<Integer, ISymbolicConfiguration>(configurations.size());
            configurationsEquivalentClasses = new HashMap<Integer, ImmutableList<ISymbolicEquivalenceClass>>();
         }
      }
   }
   
   protected Set<Term> computeInitialLocationsToIgnore() {
      Set<Term> result = new HashSet<Term>();
      IProgramVariable excVar = SymbolicExecutionUtil.extractExceptionVariable(node.proof());
      if (excVar instanceof ProgramVariable) {
         result.add(TermBuilder.DF.var((ProgramVariable)excVar));
      }
      return result;
   }

   protected Set<Term> collectSymbolicObjectsFromConditionsInSequent(Sequent sequent, Set<Term> updateCreatedObjects) throws ProofInputException {
      Set<Term> result = new LinkedHashSet<Term>();
      for (SequentFormula sf : sequent.antecedent()) {
         result.addAll(collectSymbolicObjectsFromTerm(sf.formula(), updateCreatedObjects));
      }
      return result;
   }

   protected LocationVariable createLocationVariable(String name, Sort sort) throws ProofInputException {
      final KeYJavaType kjt = getServices().getJavaInfo().getKeYJavaType(sort);
      if (kjt == null) {
         throw new ProofInputException("Can't find Java type of sort \"" + sort + "\".");
      }
      return new LocationVariable(new ProgramElementName(name), kjt);
   }

   public boolean isAnalysed() {
      synchronized (this) {
         return initialConfigurations != null && currentConfigurations != null;
      }
   }

   public int getConfigurationsCount() {
      synchronized (this) {
         assert isAnalysed();
         return configurations.size();
      }
   }
   
   public ImmutableList<ISymbolicEquivalenceClass> getEquivalenceClasses(int configurationIndex) {
      synchronized (this) {
         ImmutableList<ISymbolicEquivalenceClass> equivalentClasses = configurationsEquivalentClasses.get(Integer.valueOf(configurationIndex));
         if (equivalentClasses == null) {
            ImmutableSet<Term> configuration = configurations.get(configurationIndex);
            equivalentClasses = computeEquivalenzClasses(configuration);
            configurationsEquivalentClasses.put(Integer.valueOf(configurationIndex), equivalentClasses);
         }
         return equivalentClasses;
      }
   }
   
   public ISymbolicConfiguration getInitialConfiguration(int configurationIndex) throws ProofInputException {
      return getConfiguration(getProof().root(), initialConfigurations, configurationIndex, initialConfigurationTerm, initialLocations, pathCondition, computeInitialStateName());
   }

   protected String computeInitialStateName() {
      return getProof().root().name() + " resulting in " + computeCurrentStateName();
   }

   public ISymbolicConfiguration getCurrentConfiguration(int configurationIndex) throws ProofInputException {
      return getConfiguration(node, currentConfigurations, configurationIndex, currentConfigurationTerm, currentLocations, null, computeCurrentStateName());
   }
   
   protected String computeCurrentStateName() {
      return node.name();
   }

   protected ISymbolicConfiguration getConfiguration(Node node,
                                                     Map<Integer, ISymbolicConfiguration> confiurationsMap, 
                                                     int configurationIndex,
                                                     Term configurationTerm,
                                                     Set<ExtractValueParameter> locations,
                                                     Term pathCondition,
                                                     String stateName) throws ProofInputException {
      synchronized (this) {
         assert configurationIndex >= 0;
         assert configurationIndex < configurations.size();
         assert isAnalysed();
         ISymbolicConfiguration result = confiurationsMap.get(Integer.valueOf(configurationIndex));
         if (result == null) {
            // Get configuration
            ImmutableSet<Term> configuration = configurations.get(configurationIndex);
            ImmutableList<ISymbolicEquivalenceClass> equivalentClasses = getEquivalenceClasses(configurationIndex);
            result = computeConfiguration(node, configuration, configurationTerm, locations, equivalentClasses, pathCondition, stateName);
            confiurationsMap.put(Integer.valueOf(configurationIndex), result);
         }
         return result;
      }
   }
   
   protected ISymbolicConfiguration computeConfiguration(Node node,
                                                         ImmutableSet<Term> configuration, 
                                                         Term configurationTerm,
                                                         Set<ExtractValueParameter> locations,
                                                         ImmutableList<ISymbolicEquivalenceClass> equivalentClasses,
                                                         Term pathCondition,
                                                         String stateName) throws ProofInputException {
      if (!locations.isEmpty()) {
         // Get original updates
         Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
         ImmutableList<Term> originalUpdates = TermBuilder.DF.goBelowUpdates2(originalModifiedFormula).first;
         // Combine configuration with original updates
         Term configurationCondition = TermBuilder.DF.and(configuration);
         if (pathCondition != null) {
            configurationCondition = TermBuilder.DF.and(configurationCondition, pathCondition);
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
         for (ExtractValueParameter evp : locations) {
            additionalUpdates = additionalUpdates.append(evp.computePreUpdate());
         }
         ImmutableList<Term> newUpdates = ImmutableSLList.<Term>nil().append(TermBuilder.DF.parallel(additionalUpdates));
         Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, configurationCondition, configurationTerm, newUpdates);
         // Instantiate proof
         ApplyStrategy.ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(getProof(), sequent, StrategyProperties.SPLITTING_DELAYED);
         Term resultTerm = SymbolicExecutionUtil.extractOperatorTerm(info, configurationTerm.op());
         // Extract variable value pairs
         Set<ExecutionVariableValuePair> pairs = new LinkedHashSet<ExecutionVariableValuePair>();
         for (ExtractValueParameter param : locations) {
            ExecutionVariableValuePair pair;
            if (param.isArrayIndex()) {
               pair = new ExecutionVariableValuePair(param.getArrayIndex(), param.getSelectParentTerm(), resultTerm.sub(param.getSelectValueTermIndexInStatePredicate()));
            }
            else {
               pair = new ExecutionVariableValuePair(param.getProgramVariable(), param.getSelectParentTerm(), resultTerm.sub(param.getSelectValueTermIndexInStatePredicate()));
            }
            pairs.add(pair);
         }
         // Create symbolic configuration
         return createConfigurationFromExecutionVariableValuePairs(equivalentClasses, pairs, stateName);
      }
      else {
         // Create empty symbolic configuration
         return createConfigurationFromExecutionVariableValuePairs(equivalentClasses, new LinkedHashSet<ExecutionVariableValuePair>(), stateName);
      }
   }

   protected Term removeImplicitSubTermsFromPathCondition(Term term) {
      if (Junctor.AND == term.op()) {
         // Path condition with multiple terms combined via AND
         List<Term> newTerms = new LinkedList<Term>();
         for (Term sub : term.subs()) {
            if (!containsImplicitProgramVariable(sub)) {
               newTerms.add(sub);
            }
         }
         return TermBuilder.DF.and(newTerms);
      }
      else {
         // Only one term in path condition
         if (!containsImplicitProgramVariable(term)) {
            return term;
         }
         else {
            return TermBuilder.DF.tt();
         }
      }
   }

   protected boolean containsImplicitProgramVariable(Term t) {
      if (t.op() instanceof ProgramVariable && isImplicitProgramVariable((ProgramVariable)t.op())) {
         return true;
      }
      for (int i = 0; i < t.arity(); i++) {
         if (containsImplicitProgramVariable(t.sub(i))) {
            return true;
         }
      }
      return false;
   }

   protected boolean isImplicitProgramVariable(ProgramVariable var) {
      return var != null && var.isImplicit();
   }

   // Expected result: {.SimpleLinkedOjbects::next(.SimpleLinkedOjbects::next(x)),null,x,.SimpleLinkedOjbects::next(x)}
   protected Set<Term> collectSymbolicObjectsFromTerm(Term term, final Set<Term> updateCreatedObjects) throws ProofInputException {
      final Set<Term> result = new LinkedHashSet<Term>();
      term.execPreOrder(new Visitor() {
         @Override
         public void visit(Term visited) {
            if (SymbolicExecutionUtil.hasReferenceSort(getServices(), visited) && 
                visited.freeVars().isEmpty() &&
                !updateCreatedObjects.contains(visited)) {
               result.add(visited);
            }
         }
      });
      return result;
   }

   protected Set<Term> filterOutNewupdateCreatedObjects(Set<Term> symbolicObjectsResultingInCurrentState, Set<Term> updateCreatedObjects) throws ProofInputException {
      Set<Term> result = new LinkedHashSet<Term>();
      for (Term symbolicObject : symbolicObjectsResultingInCurrentState) {
         if (!updateCreatedObjects.contains(symbolicObject)) {
            result.add(symbolicObject);
         }
      }
      return result;
   }
   
   protected Sequent computeInitialConditionsSequent(Term pathCondition) { // DebuggerPO.setUp in old editor
      // Get original sequent
      Sequent originalSequent = getProof().root().sequent();
      // Add path condition to antecedent
      Semisequent newAntecedent = originalSequent.antecedent();
      newAntecedent = newAntecedent.insertLast(new SequentFormula(pathCondition)).semisequent();
      // Remove everything after modality from sequent
      Semisequent newSuccedent = Semisequent.EMPTY_SEMISEQUENT;
      for (SequentFormula sf : originalSequent.succedent()) {
         Term term = sf.formula();
         if (Junctor.IMP.equals(term.op())) {
            Term newImplication = TermBuilder.DF.imp(term.sub(0), TermBuilder.DF.ff());
            newSuccedent = newSuccedent.insertLast(new SequentFormula(newImplication)).semisequent();
            // Updates are not required, because TermBuilder.DF.apply(updates, true) is just true
         }
         else {
            newSuccedent = newSuccedent.insertLast(sf).semisequent();
         }
      }
      return Sequent.createSequent(newAntecedent, newSuccedent);
   }
   
   protected Sequent addPathCondition(Sequent initialConditionsSequent, Term pathCondition) { // DebuggerPO.setUp in old debugger
      SequentChangeInfo info = initialConditionsSequent.addFormula(new SequentFormula(pathCondition), true, false);
      return info.sequent();
   }
   
   protected void applyCutRules(ProofStarter starter, Set<Term> symbolicObjects) { // StateVisualization.applyCuts in old debugger
      int maxProofSteps = 8000;
      for (Term first : symbolicObjects) {
         for (Term second : symbolicObjects) {
            if (!first.equals(second)) {
               Term equalTerm = TermBuilder.DF.equals(first, second);
               applyCut(starter, equalTerm, maxProofSteps);
            }
         }
      }
      starter.setMaxRuleApplications(maxProofSteps);
      starter.start();
   }

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

   protected List<ImmutableSet<Term>> computeInstanceConfigurationsFromGoals(Proof proof) {
      Set<ImmutableSet<Term>> resultSet = new LinkedHashSet<ImmutableSet<Term>>();
      Node root = proof.root();
      for (Goal goal : proof.openGoals()) {
         resultSet.add(getAppliedCutsSet(goal.node(), root));
      }
      return new ArrayList<ImmutableSet<Term>>(resultSet);
   }
   
   private ImmutableSet<Term> getAppliedCutsSet(Node n, Node root) {      
      ImmutableSet<Term> result = DefaultImmutableSet.<Term>nil();
      if (!root.find(n)) {
          throw new RuntimeException("node n ist not a childs of node root");
      }

      while (!(n.serialNr() == root.serialNr())) {
          final Node oldN = n;
          n = n.parent();
          if (n.getAppliedRuleApp() instanceof NoPosTacletApp) {
              NoPosTacletApp npta = (NoPosTacletApp) n.getAppliedRuleApp();
              if (npta.taclet().name().toString().toUpperCase().equals("CUT")) {
                  Term inst = (Term) npta.instantiations().lookupEntryForSV(
                          new Name("cutFormula")).value().getInstantiation();
                  if (n.child(1) == oldN)
                      inst = TermBuilder.DF.not(inst);
                  result = result.add(inst);

              }
          }
      }

      return result;

  }
   



   protected Set<ExtractValueParameter> sequentToLocations(Sequent sequent, Set<Term> updateCreatedObjects) throws ProofInputException {
      Set<ExtractValueParameter> result = new LinkedHashSet<ExtractValueParameter>();
      for (SequentFormula sf : sequent.antecedent()) {
         result.addAll(termToLocations(sf.formula(), updateCreatedObjects));
      }
      for (SequentFormula sf : sequent.succedent()) {
         Term term = sf.formula();
         if (Junctor.IMP != term.op()) {
            result.addAll(termToLocations(term, updateCreatedObjects));
         }
      }
      return result;
   }
   
   protected Set<ExtractValueParameter> termToLocations(Term term, Set<Term> updateCreatedObjects) throws ProofInputException {
      Set<ExtractValueParameter> result = new LinkedHashSet<ExtractValueParameter>();
      fillLocationsFromTerm(result, term, updateCreatedObjects);
      return result;
   }
   
   protected void fillLocationsFromTerm(Set<ExtractValueParameter> toFill, Term term, Set<Term> updateCreatedObjects) throws ProofInputException {
      final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
      if (term.op() instanceof ProgramVariable) {
         ProgramVariable var = (ProgramVariable)term.op();
         if (heapLDT.getHeap() != term.op() && !isImplicitProgramVariable(var) && !updateCreatedObjects.contains(term)) {
            toFill.add(new ExtractValueParameter(var));
         }
      }
      else {
         Sort sort = heapLDT.getSortOfSelect(term.op());
         if (sort != null) {
            ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, term.sub(2));
            if (var != null) {
               if (!isImplicitProgramVariable(var)) {
                  if (var.isStatic()) {
                     toFill.add(new ExtractValueParameter(var));
                  }
                  else {
                     Term selectTerm = term.sub(1);
                     if (selectTerm.op() instanceof ProgramVariable) {
                        toFill.add(new ExtractValueParameter((ProgramVariable)selectTerm.op()));
                     }
                     toFill.add(new ExtractValueParameter(var, selectTerm));
                  }
               }
            }
            else {
               int arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, term.sub(2));
               if (arrayIndex >= 0) {
                  Term selectTerm = term.sub(1);
                  if (selectTerm.op() instanceof ProgramVariable) {
                     toFill.add(new ExtractValueParameter((ProgramVariable)selectTerm.op()));
                  }
                  toFill.add(new ExtractValueParameter(arrayIndex, selectTerm));
               }
               else {
                  throw new ProofInputException("Unsupported select statement \"" + term + "\".");
               }
            }
         }
         else if (heapLDT.getLength() == term.op()) {
            ProgramVariable var = getServices().getJavaInfo().getArrayLength();
            toFill.add(new ExtractValueParameter(var, term.sub(0)));
         }
         else {
            for (Term sub : term.subs()) {
               fillLocationsFromTerm(toFill, sub, updateCreatedObjects);
            }
         }
      }
   }
   
   // EXPECTED:
   // .SimpleLinkedOjbects::value(x),
   // .SimpleLinkedOjbects::value(.SimpleLinkedOjbects::next(x))
   // .SimpleLinkedOjbects::value(.SimpleLinkedOjbects::next(.SimpleLinkedOjbects::next(x)))
   protected void collectLocationsFromUpdates(Sequent sequent, Set<ExtractValueParameter> toFill, Set<Term> updateCreatedObjectsToFill, Set<Term> updateValueObjectsToFill) throws ProofInputException {
      Term updateApplication = findUpdates(sequent);
      if (updateApplication == null) {
         throw new ProofInputException("Can't find update application in \"" + sequent + "\".");
      }
      Term topUpdate = UpdateApplication.getUpdate(updateApplication);
      fillLocations(topUpdate, toFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
   }
   
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

   protected void fillLocations(Term update, 
                                Set<ExtractValueParameter> toFill, 
                                Set<Term> updateCreatedObjectsToFill, 
                                Set<Term> updateValueObjectsToFill) throws ProofInputException {
      if (update.op() instanceof UpdateJunctor) {
         for (Term sub : update.subs()) {
            fillLocations(sub, toFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
         }
      }
      else if (update.op() instanceof ElementaryUpdate) {
         ElementaryUpdate eu = (ElementaryUpdate)update.op();
         if (SymbolicExecutionUtil.isHeapUpdate(getServices(), update)) {
            fillHeapLocations(update.sub(0), toFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
         }
         else if (eu.lhs() instanceof ProgramVariable) {
            ProgramVariable var = (ProgramVariable)eu.lhs();
            if (var.getContainerType() != null && !isImplicitProgramVariable(var)) { // Make sure that it is a location in the source code and not an internal one of the proof
               toFill.add(new ExtractValueParameter(var));
            }
            if (SymbolicExecutionUtil.hasReferenceSort(getServices(), update.sub(0))) {
               updateValueObjectsToFill.add(update.sub(0));
            }
         }
         else {
            throw new ProofInputException("Unsupported update operator \"" + eu.lhs() + "\".");
         }
      }
      else {
         throw new ProofInputException("Unsupported update operator \"" + update.op() + "\".");
      }
   }
   
   protected void fillHeapLocations(Term term, 
                                    Set<ExtractValueParameter> toFill, 
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
                  toFill.add(new ExtractValueParameter(var, selectArgument.sub(1)));
               }
            }
            else {
               int arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, selectArgument.sub(2));
               if (arrayIndex >= 0) {
                  toFill.add(new ExtractValueParameter(arrayIndex, selectArgument.sub(1)));
               }
               else {
                  throw new ProofInputException("Unsupported select statement \"" + term + "\".");
               }
            }
         }
         else if (selectArgument.op() instanceof IProgramVariable) {
            ProgramVariable var = (ProgramVariable)selectArgument.op();
            if (!isImplicitProgramVariable(var)) {
               toFill.add(new ExtractValueParameter(var));
            }
         }
         else if (heapLDT.getNull() == selectArgument.op()) {
            // Static fields have a null term as select argument.
         }
         else {
            throw new ProofInputException("Unsupported operator in select argument of heap update \"" + selectArgument.op() + "\".");
         }
         // Add select value term to result
         ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, term.sub(2));
         if (var != null) {
            if (!isImplicitProgramVariable(var)) {
               if (var.isStatic()) {
                  toFill.add(new ExtractValueParameter(var));
               }
               else {
                  toFill.add(new ExtractValueParameter(var, term.sub(1)));
               }
            }
         }
         else {
            int arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, term.sub(2));
            if (arrayIndex >= 0) {
               toFill.add(new ExtractValueParameter(arrayIndex, term.sub(1)));
            }
            else {
               throw new ProofInputException("Unsupported select statement \"" + term + "\".");
            }
         }
         if (SymbolicExecutionUtil.hasReferenceSort(getServices(), term.sub(3)) && term.sub(3).op() instanceof ProgramVariable) {
            updateValueObjectsToFill.add(term.sub(3));
         }
         // Iterate over child heap modifications
         fillHeapLocations(term.sub(0), toFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
      }
      else if (term.op() == heapLDT.getCreate()) {
         updateCreatedObjectsToFill.add(term.sub(1));
         // Iterate over child heap modifications
         fillHeapLocations(term.sub(0), toFill, updateCreatedObjectsToFill, updateValueObjectsToFill);
      }
      else if (term.op() == heapLDT.getHeap()) {
         // Initial Heap, nothing to do
      }
      else {
         throw new ProofInputException("Unsupported operator in heap update \"" + term.op() + "\".");
      }
   }

   protected Term createConfigurationPredicateAndTerm(Set<ExtractValueParameter> valueSelectParameter) {
      List<Term> argumentsList = new LinkedList<Term>();
      int argumentIndex = -1;
      for (ExtractValueParameter param : valueSelectParameter) {
         argumentsList.add(param.computePreParentTerm());
         param.setSelectParentTermIndexInStatePredicate(++argumentIndex);
         argumentsList.add(param.computePreValueTerm());
         param.setSelectValueTermIndexInStatePredicate(++argumentIndex);
      }
      Term[] arguments = argumentsList.toArray(new Term[argumentsList.size()]);
      Sort[] sorts = new Sort[arguments.length];
      for (int i = 0; i < sorts.length; i++) {
         sorts[i] = arguments[i].sort();
      }
      // Create predicate which will be used in formulas to store the value interested in.
      Function newPredicate = new Function(new Name(TermBuilder.DF.newName(getServices(), "ConfigurationPredicate")), Sort.FORMULA, sorts);
      // Create formula which contains the value interested in.
      Term newTerm = TermBuilder.DF.func(newPredicate, arguments);
      return newTerm;
   }

   protected ImmutableList<ISymbolicEquivalenceClass> computeEquivalenzClasses(ImmutableSet<Term> configuration) {
      ImmutableList<ISymbolicEquivalenceClass> result = ImmutableSLList.nil();
      for (Term term : configuration) {
         if (Junctor.NOT != term.op()) {
            assert term.op() == Equality.EQUALS;
            final Iterator<Term> iter = term.subs().iterator();
            ISymbolicEquivalenceClass ec = null;
            while (ec == null && iter.hasNext()) {
               ec = findEquivalentClass(result, iter.next());
            }
            if (ec == null) {
               ec = new SymbolicEquivalenceClass(getServices());
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
   
   protected ISymbolicEquivalenceClass findEquivalentClass(ImmutableList<ISymbolicEquivalenceClass> equivalentClasses, final Term term) {
      return JavaUtil.search(equivalentClasses, new IFilter<ISymbolicEquivalenceClass>() {
         @Override
         public boolean select(ISymbolicEquivalenceClass element) {
            return element.containsTerm(term);
         }
      });
   }
   
   protected ISymbolicConfiguration createConfigurationFromExecutionVariableValuePairs(ImmutableList<ISymbolicEquivalenceClass> equivalentClasses, 
                                                                                       Set<ExecutionVariableValuePair> pairs,
                                                                                       String stateName) {
      SymbolicConfiguration result = new SymbolicConfiguration(equivalentClasses);
      // Create state
      SymbolicState state = new SymbolicState(stateName);
      result.setState(state);
      // Create objects
      Map<Term, SymbolicObject> objects = new HashMap<Term, SymbolicObject>();
      for (ExecutionVariableValuePair pair : pairs) {
         Term parent = pair.getParent();
         if (parent != null) {
            SymbolicObject object = objects.get(parent);
            if (object == null) {
               ISymbolicEquivalenceClass equivalentClass = findEquivalentClass(equivalentClasses, parent);
               if (equivalentClass == null || // New created object which is not part of the path condition
                   equivalentClass.getRepresentative() == parent) { // Representative object part of path condition
                  object = new SymbolicObject(getServices(), parent);
                  objects.put(parent, object);
                  result.addObject(object);
               }
            }
         }
         Term value = pair.getValue();
         if (value != null && SymbolicExecutionUtil.hasReferenceSort(getServices(), value)) {
            SymbolicObject object = objects.get(value);
            if (object == null) {
               ISymbolicEquivalenceClass equivalentClass = findEquivalentClass(equivalentClasses, value);
               if (equivalentClass == null || // New created object which is not part of the path condition
                   equivalentClass.getRepresentative() == value) { // Representative object part of path condition
                  object = new SymbolicObject(getServices(), value);
                  objects.put(value, object);
                  result.addObject(object);
               }
            }
         }
      }
      // Fill objects and state with association and values
      for (ExecutionVariableValuePair pair : pairs) {
         // Find parent object/state
         Term parent = pair.getParent();
         Term valueTerm = pair.getValue();
         AbstractSymbolicAssociationValueContainer container;
         if (parent != null) {
            container = objects.get(parent);
         }
         else {
            if (!objectsAndLocationsToIgnore.contains(valueTerm)) {
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
                  association = new SymbolicAssociation(pair.getArrayIndex(), target);
               }
               else {
                  association = new SymbolicAssociation(pair.getProgramVariable(), target);
               }
               container.addAssociation(association);
            }
            else {
               SymbolicValue value;
               if (pair.isArrayIndex()) {
                  value = new SymbolicValue(getServices(), pair.getArrayIndex(), valueTerm);
               }
               else {
                  value = new SymbolicValue(getServices(), pair.getProgramVariable(), valueTerm);
               }
               container.addValue(value);
            }
         }
      }
      return result;
   }
   
   /**
    * Returns the {@link Proof} of the analyzed {@link Node}.
    * @return The {@link Proof} of the analyzed {@link Node}.
    */
   protected Proof getProof() {
      return node.proof();
   }
   
   /**
    * Returns the {@link Services} of the analyzed {@link Node}.
    * @return The {@link Services} of the analyzed {@link Node}.
    */
   protected Services getServices() {
      return getProof().getServices();
   }
   
   protected class ExtractValueParameter {
      private ProgramVariable programVariable;
      
      private int arrayIndex;
      
      private Term selectParentTerm;
      
      private int selectParentTermIndexInStatePredicate;

      private int selectValueTermIndexInStatePredicate;

      private LocationVariable preVariable;

      public ExtractValueParameter(ProgramVariable programVariable) throws ProofInputException {
         this(programVariable, null);
      }

      public ExtractValueParameter(ProgramVariable programVariable, Term selectParentTerm) throws ProofInputException {
         assert programVariable != null;
         this.programVariable = programVariable;
         this.selectParentTerm = selectParentTerm;
         this.preVariable = createLocationVariable("Pre" + preVariableIndex++, selectParentTerm != null ? selectParentTerm.sort() : programVariable.sort());
         this.arrayIndex = -1;
      }
      
      public ExtractValueParameter(int arrayIndex, Term selectParentTerm) throws ProofInputException {
         assert selectParentTerm != null;
         this.arrayIndex = arrayIndex;
         this.selectParentTerm = selectParentTerm;
         this.preVariable = createLocationVariable("Pre" + preVariableIndex++, selectParentTerm.sort());
      }

      public boolean isArrayIndex() {
         return arrayIndex >= 0;
      }
      
      public int getArrayIndex() {
         return arrayIndex;
      }

      public Term computePreUpdate() {
         Term originalTerm = selectParentTerm != null ? selectParentTerm : TermBuilder.DF.var(programVariable);
         return TermBuilder.DF.elementary(getServices(), preVariable, originalTerm);
      }
      
      public Term computePreParentTerm() {
         return TermBuilder.DF.var(preVariable);
      }
      
      public Term computePreValueTerm() {
         if (selectParentTerm != null) {
            if (isArrayIndex()) {
               Term idx = TermBuilder.DF.zTerm(getServices(), "" + arrayIndex);
               return TermBuilder.DF.dotArr(getServices(), selectParentTerm, idx);
            }
            else {
               if (getServices().getJavaInfo().getArrayLength() == programVariable) {
                  // Special handling for length attribute of arrays
                  Function function = getServices().getTypeConverter().getHeapLDT().getLength();
                  return TermBuilder.DF.func(function, computePreParentTerm());
               }
               else {
                  Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)programVariable, getServices());
                  return TermBuilder.DF.dot(getServices(), programVariable.sort(), computePreParentTerm(), function);
               }
            }
         }
         else {
            if (programVariable.isStatic()) {
               Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)programVariable, getServices());
               return TermBuilder.DF.staticDot(getServices(), programVariable.sort(), function);
            }
            else {
               return TermBuilder.DF.var(programVariable);
            }
         }
      }

      public ProgramVariable getProgramVariable() {
         return programVariable;
      }

      public Term getSelectParentTerm() {
         return selectParentTerm;
      }

      public int getSelectParentTermIndexInStatePredicate() {
         return selectParentTermIndexInStatePredicate;
      }

      public void setSelectParentTermIndexInStatePredicate(int selectParentTermIndexInStatePredicate) {
         this.selectParentTermIndexInStatePredicate = selectParentTermIndexInStatePredicate;
      }

      public int getSelectValueTermIndexInStatePredicate() {
         return selectValueTermIndexInStatePredicate;
      }

      public void setSelectValueTermIndexInStatePredicate(int selectValueTermIndexInStatePredicate) {
         this.selectValueTermIndexInStatePredicate = selectValueTermIndexInStatePredicate;
      }

      @Override
      public String toString() {
         if (isArrayIndex()) {
            return "[" + arrayIndex + "] " + (selectParentTerm != null ? " of " + selectParentTerm : "");
         }
         else {
            return programVariable + (selectParentTerm != null ? " of " + selectParentTerm : "");
         }
      }
   }
   
   protected static class ExecutionVariableValuePair {
      private int arrayIndex;
      private ProgramVariable programVariable;
      private Term parent;
      private Term value;

      public ExecutionVariableValuePair(ProgramVariable programVariable, Term parent, Term value) {
         assert programVariable != null;
         assert value != null;
         this.programVariable = programVariable;
         this.parent = parent;
         this.value = value;
         this.arrayIndex = -1;
      }

      public ExecutionVariableValuePair(int arrayIndex, Term parent, Term value) {
         assert parent != null;
         assert value != null;
         this.arrayIndex = arrayIndex;
         this.parent = parent;
         this.value = value;
      }

      public ProgramVariable getProgramVariable() {
         return programVariable;
      }

      public Term getParent() {
         return parent;
      }

      public Term getValue() {
         return value;
      }
      
      public boolean isArrayIndex() {
         return arrayIndex >= 0;
      }

      public int getArrayIndex() {
         return arrayIndex;
      }

      @Override
      public boolean equals(Object obj) {
         if (obj instanceof ExecutionVariableValuePair) {
            ExecutionVariableValuePair other = (ExecutionVariableValuePair)obj;
            return isArrayIndex() ? getArrayIndex() == other.getArrayIndex() : getProgramVariable().equals(other.getProgramVariable()) &&
                   getParent() != null ? getParent().equals(other.getParent()) : other.getParent() == null &&
                   getValue().equals(other.getValue());
         }
         else {
            return false;
         }
      }

      @Override
      public int hashCode() {
         int result = 17;
         result = 31 * result + (isArrayIndex() ? getArrayIndex() : getProgramVariable().hashCode());
         result = 31 * result + (getParent() != null ? getParent().hashCode() : 0);
         result = 31 * result + getValue().hashCode();
         return result;
      }

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
