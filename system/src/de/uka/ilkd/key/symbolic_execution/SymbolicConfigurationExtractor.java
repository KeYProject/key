package de.uka.ilkd.key.symbolic_execution;

import java.util.ArrayList;
import java.util.HashMap;
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
import de.uka.ilkd.key.logic.SemisequentChangeInfo;
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

public class SymbolicConfigurationExtractor {
   private Node node;
   
   private List<ImmutableSet<Term>> configurations;
   
   private Map<Integer, ISymbolicConfiguration> currentConfigurations;
   
   private Set<ExtractValueParameter> currentLocations;
   
   private Term currentConfigurationTerm;
   
   private Map<Integer, ISymbolicConfiguration> initialConfigurations;
   
   private Set<ExtractValueParameter> initialLocations;
   
   private Term initialConfigurationTerm;
   
   private int preVariableIndex = 0;
   
   public SymbolicConfigurationExtractor(Node node) {
      assert node != null;
      this.node = node;
   }

   public void analyse() throws ProofInputException {
      synchronized (this) {
         if (!isAnalysed()) {
            // Get path condition
            Term pathCondition = SymbolicExecutionUtil.computePathCondition(node, true);
            Term pathConditionWithoutImplicits = removeImplicitSubTermsFromPathCondition(pathCondition);
            // Collect all symbolic objects mentioned in the path condition
            Set<Term> symbolicObjectsInPathCondition = collectSymbolicObjectsFromPathCondition(pathConditionWithoutImplicits);
            // Compute a sequent with the initial conditions of the proof without modality
            Sequent initialConditionsSequent = computeInitialConditionsSequent();
            // Instantiate proof in which equivalent classes of symbolic objects in path conditions are computed
            ProofStarter equivalentClassesProofStarter = SymbolicExecutionUtil.createSideProof(getProof(), initialConditionsSequent);
            // Apply cut rules to compute equivalent classes
            applyCutRules(equivalentClassesProofStarter, symbolicObjectsInPathCondition);
            // Finish proof automatically
            runProof(equivalentClassesProofStarter);
            // Compute the available instance configurations via the opened goals of the equivalent proof.
            configurations = computeInstanceConfigurationsFromGoals(equivalentClassesProofStarter.getProof());
            // Collect all symbolic objects used in updates
            initialLocations = objectsToLocations(symbolicObjectsInPathCondition);
            currentLocations = collectLocationsFromUpdates(node.sequent());
            // Create predicate required for state computation
            initialConfigurationTerm = createConfigurationPredicateAndTerm(initialLocations);
            currentConfigurationTerm = createConfigurationPredicateAndTerm(currentLocations);
            // Create configuration maps which are filled lazily
            initialConfigurations = new HashMap<Integer, ISymbolicConfiguration>(configurations.size());
            currentConfigurations = new HashMap<Integer, ISymbolicConfiguration>(configurations.size());
         }
      }
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
   
   public ISymbolicConfiguration getInitialConfiguration(int configurationIndex) throws ProofInputException {
      return getConfiguration(getProof().root(), initialConfigurations, configurationIndex, initialConfigurationTerm, initialLocations);
   }
   
   public ISymbolicConfiguration getCurrentConfiguration(int configurationIndex) throws ProofInputException {
      return getConfiguration(node, currentConfigurations, configurationIndex, currentConfigurationTerm, currentLocations);
   }
   
   protected ISymbolicConfiguration getConfiguration(Node node,
                                                     Map<Integer, ISymbolicConfiguration> confiurationsMap, 
                                                     int configurationIndex,
                                                     Term configurationTerm,
                                                     Set<ExtractValueParameter> locations) throws ProofInputException {
      synchronized (this) {
         assert configurationIndex >= 0;
         assert configurationIndex < configurations.size();
         assert isAnalysed();
         ISymbolicConfiguration result = confiurationsMap.get(Integer.valueOf(configurationIndex));
         if (result == null) {
            // Get configuration
            ImmutableSet<Term> configuration = configurations.get(configurationIndex);
            result = computeConfiguration(node, configuration, configurationTerm, locations);
            confiurationsMap.put(Integer.valueOf(configurationIndex), result);
         }
         return result;
      }
   }
   
   protected ISymbolicConfiguration computeConfiguration(Node node,
                                                         ImmutableSet<Term> configuration, 
                                                         Term configurationTerm,
                                                         Set<ExtractValueParameter> locations) throws ProofInputException {
      // Get original updates
      Term originalModifiedFormula = node.getAppliedRuleApp().posInOccurrence().constrainedFormula().formula();
      ImmutableList<Term> originalUpdates = TermBuilder.DF.goBelowUpdates2(originalModifiedFormula).first;
      // Combine configuration with original updates
      Term configurationCondition = TermBuilder.DF.and(configuration);
      ImmutableList<Term> additionalUpdates = ImmutableSLList.nil();
      for (Term originalUpdate : originalUpdates) {
         if (UpdateJunctor.PARALLEL_UPDATE != originalUpdate.op()) {
            throw new ProofInputException("Expected that update is a parallel update but found \"" + originalUpdate.op() + "\".");
         }
         additionalUpdates = additionalUpdates.append(originalUpdate.subs());
      }
      for (ExtractValueParameter evp : locations) {
         additionalUpdates = additionalUpdates.append(evp.computePreUpdate());
      }
      ImmutableList<Term> newUpdates = ImmutableSLList.<Term>nil().append(TermBuilder.DF.parallel(additionalUpdates));
      Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, configurationCondition, configurationTerm, newUpdates);
      // Instantiate proof
      ApplyStrategy.ApplyStrategyInfo info = SymbolicExecutionUtil.startSideProof(getProof(), sequent);
      Term resultTerm = SymbolicExecutionUtil.extractOperatorTerm(info, configurationTerm.op());
      // Extract variable value pairs
      Set<ExecutionVariableValuePair> pairs = new LinkedHashSet<ExecutionVariableValuePair>();
      for (ExtractValueParameter param : locations) {
         ExecutionVariableValuePair pair = new ExecutionVariableValuePair(param.getProgramVariable(), param.getSelectParentTerm(), resultTerm.sub(param.getSelectValueTermIndexInStatePredicate()));
         pairs.add(pair);
      }
      // Create symbolic configuration
      List<SymbolicEquivalenceClass> equivalentClasses = computeEquivalenzClasses(configuration);
      return createConfigurationFromExecutionVariableValuePairs(equivalentClasses, pairs);
   }
   
   protected Term removeImplicitSubTermsFromPathCondition(Term andTerm) {
      List<Term> newTerms = new LinkedList<Term>();
      for (Term sub : andTerm.subs()) {
         if (!containsImplicitProgramVariable(sub)) {
            newTerms.add(sub);
         }
      }
      return TermBuilder.DF.and(newTerms);
   }

   protected boolean containsImplicitProgramVariable(Term t) {
      if (t.op() instanceof ProgramVariable && ((ProgramVariable)t.op()).isImplicit()) {
         return true;
      }
      for (int i = 0; i < t.arity(); i++) {
         if (containsImplicitProgramVariable(t.sub(i))) {
            return true;
         }
      }
      return false;
   }

   // Expected result: {.SimpleLinkedOjbects::next(.SimpleLinkedOjbects::next(x)),null,x,.SimpleLinkedOjbects::next(x)}
   protected Set<Term> collectSymbolicObjectsFromPathCondition(Term pathCondition) throws ProofInputException {
      final Set<Term> result = new LinkedHashSet<Term>();
      pathCondition.execPreOrder(new Visitor() {
         @Override
         public void visit(Term visited) {
            if (SymbolicExecutionUtil.hasReferenceSort(getServices(), visited) && 
                visited.freeVars().isEmpty()) {
               result.add(visited);
            }
         }
      });
      return result;
   }
   
   protected Sequent computeInitialConditionsSequent() { // DebuggerPO.setUp in old editor
      // Get original sequent
      Sequent originalSequent = getProof().root().sequent();
      // Remove everything after modality from sequent
      Semisequent newSuccedent = Semisequent.EMPTY_SEMISEQUENT;
      for (SequentFormula sf : originalSequent.succedent()) {
         Term term = sf.formula();
         if (Junctor.IMP.equals(term.op())) {
            SemisequentChangeInfo info = newSuccedent.insertLast(new SequentFormula(term.sub(0)));
            newSuccedent = info.semisequent();
            // TODO: Are updates required? Because TermBuilder.DF.apply(updates, true) is just true
         }
         else {
            newSuccedent.insertLast(sf);
         }
      }
      return Sequent.createSequent(originalSequent.antecedent(), newSuccedent);
   }
   
   protected Sequent addPathCondition(Sequent initialConditionsSequent, Term pathCondition) { // DebuggerPO.setUp in old debugger
      SequentChangeInfo info = initialConditionsSequent.addFormula(new SequentFormula(pathCondition), true, false);
      return info.sequent();
   }
   
   protected void applyCutRules(ProofStarter starter, Set<Term> symbolicObjectsInPathCondition) { // StateVisualization.applyCuts in old debugger
      int maxProofSteps = 8000;
      for (Term first : symbolicObjectsInPathCondition) {
         for (Term second : symbolicObjectsInPathCondition) {
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

   protected void runProof(ProofStarter proof) {
      SymbolicExecutionUtil.startSideProof(getProof(), proof, StrategyProperties.SPLITTING_NORMAL);
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
   

   
   protected Set<ExtractValueParameter> objectsToLocations(Set<Term> symbolicObjects) throws ProofInputException {
      final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
      Set<ExtractValueParameter> result = new LinkedHashSet<ExtractValueParameter>();
      for (Term obj : symbolicObjects) {
         if (obj.op() instanceof ProgramVariable) {
            ProgramVariable var = (ProgramVariable)obj.op();
            result.add(new ExtractValueParameter(var, TermBuilder.DF.var(var)));
         }
         else if (heapLDT.getSortOfSelect(obj.op()) != null) {
            ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, obj.sub(2));
            result.add(new ExtractValueParameter(var, obj.sub(1), obj));
         }
         else {
            throw new ProofInputException("Unsupported object operator \"" + obj.op() + "\".");
         }
      }
      return result;
   }
   
   // EXPECTED:
   // .SimpleLinkedOjbects::value(x),
   // .SimpleLinkedOjbects::value(.SimpleLinkedOjbects::next(x))
   // .SimpleLinkedOjbects::value(.SimpleLinkedOjbects::next(.SimpleLinkedOjbects::next(x)))
   protected Set<ExtractValueParameter> collectLocationsFromUpdates(Sequent sequent) throws ProofInputException {
      Set<ExtractValueParameter> result = new LinkedHashSet<ExtractValueParameter>();
      Term updateApplication = findUpdates(sequent);
      if (updateApplication == null) {
         throw new ProofInputException("Can't find update application in \"" + sequent + "\".");
      }
      Term topUpdate = UpdateApplication.getUpdate(updateApplication);
      fillLocations(topUpdate, result);
      return result;
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

   protected void fillLocations(Term update, Set<ExtractValueParameter> toFill) throws ProofInputException {
      if (update.op() instanceof UpdateJunctor) {
         for (Term sub : update.subs()) {
            fillLocations(sub, toFill);
         }
      }
      else if (update.op() instanceof ElementaryUpdate) {
         ElementaryUpdate eu = (ElementaryUpdate)update.op();
         if (SymbolicExecutionUtil.isHeapUpdate(getServices(), update)) {
            fillHeapLocations(update.sub(0), toFill);
         }
         else if (eu.lhs() instanceof ProgramVariable) {
            ProgramVariable var = (ProgramVariable)eu.lhs();
            if (var.getContainerType() != null) { // Make sure that it is a location in the source code and not an internal one of the proof
               toFill.add(new ExtractValueParameter(var, TermBuilder.DF.var(var)));
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
   
   protected void fillHeapLocations(Term term, Set<ExtractValueParameter> toFill) throws ProofInputException {
      final HeapLDT heapLDT = getServices().getTypeConverter().getHeapLDT();
      if (term.op() == heapLDT.getStore()) {
         // Add select object term to result
         Term selectArgument = term.sub(1);
         if (heapLDT.getSortOfSelect(selectArgument.op()) != null) {
            ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, selectArgument.sub(2));
            toFill.add(new ExtractValueParameter(var, selectArgument.sub(1), selectArgument));
         }
         else if (selectArgument.op() instanceof IProgramVariable) {
            ProgramVariable var = (ProgramVariable)selectArgument.op();
            toFill.add(new ExtractValueParameter(var, TermBuilder.DF.var(var)));
         }
         else {
            throw new ProofInputException("Unsupported operator in select argument of heap update \"" + selectArgument.op() + "\".");
         }
         // Add select value term to result
         ProgramVariable var = SymbolicExecutionUtil.getProgramVariable(getServices(), heapLDT, term.sub(2));
         Term selectValueTerm = TermBuilder.DF.dot(getServices(), var.sort(), selectArgument, term.sub(2));
         toFill.add(new ExtractValueParameter(var, term.sub(1), selectValueTerm));
         // Iterate over child heap modifications
         fillHeapLocations(term.sub(0), toFill);
      }
      else if (term.op() == heapLDT.getCreate()) {
         // TODO: Really nothing to do?
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

   protected List<SymbolicEquivalenceClass> computeEquivalenzClasses(ImmutableSet<Term> configuration) {
      List<SymbolicEquivalenceClass> result = new LinkedList<SymbolicEquivalenceClass>();
      for (Term term : configuration) {
         if (Junctor.NOT != term.op()) {
            assert term.op() == Equality.EQUALS;
            final Iterator<Term> iter = term.subs().iterator();
            SymbolicEquivalenceClass ec = null;
            while (ec == null && iter.hasNext()) {
               ec = findEquivalentClass(result, iter.next());
            }
            if (ec == null) {
               ec = new SymbolicEquivalenceClass(getServices());
               result.add(ec); 
            }
            for (Term sub : term.subs()) {
               if (!ec.containsTerm(sub)) {
                  ec.addTerm(sub);
               }
            }
         }
      }
      return result;
   }
   
   protected SymbolicEquivalenceClass findEquivalentClass(List<SymbolicEquivalenceClass> equivalentClasses, final Term term) {
      return JavaUtil.search(equivalentClasses, new IFilter<SymbolicEquivalenceClass>() {
         @Override
         public boolean select(SymbolicEquivalenceClass element) {
            return element.containsTerm(term);
         }
      });
   }
   
   protected ISymbolicConfiguration createConfigurationFromExecutionVariableValuePairs(List<SymbolicEquivalenceClass> equivalentClasses, Set<ExecutionVariableValuePair> pairs) {
      SymbolicConfiguration result = new SymbolicConfiguration();
      // Add equivalence classes
      for (SymbolicEquivalenceClass ec : equivalentClasses) {
         result.addEquivalenceClass(ec);
      }
      // Create state
      SymbolicState state = new SymbolicState();
      result.setState(state);
      // Create objects
      Map<Term, SymbolicObject> objects = new HashMap<Term, SymbolicObject>();
      for (ExecutionVariableValuePair pair : pairs) {
         Term parent = pair.getParent();
         if (parent != null) {
            SymbolicObject object = objects.get(parent);
            if (object == null) {
               SymbolicEquivalenceClass equivalentClass = findEquivalentClass(equivalentClasses, parent);
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
               SymbolicEquivalenceClass equivalentClass = findEquivalentClass(equivalentClasses, value);
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
         AbstractSymbolicAssociationValueContainer container;
         if (parent != null) {
            container = objects.get(parent);
         }
         else {
            container = state;
         }
         // Check if a container was found, if not it is an less important equivalent object
         if (container != null) {
            // Check if it is an association
            SymbolicObject target = objects.get(pair.getValue());
            if (target != null) {
               SymbolicAssociation association = new SymbolicAssociation(pair.getProgramVariable(), target);
               container.addAssociation(association);
            }
            else {
               SymbolicValue value = new SymbolicValue(getServices(), pair.getProgramVariable(), pair.getValue());
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
      
      private Term selectParentTerm;
      
      private Term selectValueTerm;
      
      private int selectParentTermIndexInStatePredicate;

      private int selectValueTermIndexInStatePredicate;

      private LocationVariable preVariable;

      public ExtractValueParameter(ProgramVariable programVariable, Term selectValueTerm) throws ProofInputException {
         this(programVariable, null, selectValueTerm);
      }
      
      public ExtractValueParameter(ProgramVariable programVariable, Term selectParentTerm, Term selectValueTerm) throws ProofInputException {
         this.programVariable = programVariable;
         this.selectParentTerm = selectParentTerm;
         this.selectValueTerm = selectValueTerm;
         this.preVariable = createLocationVariable("Pre" + preVariableIndex++, selectParentTerm != null ? selectParentTerm.sort() : programVariable.sort());
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
            Function function = getServices().getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable)programVariable, getServices());
            return TermBuilder.DF.dot(getServices(), programVariable.sort(), computePreParentTerm(), function);
         }
         else {
            return TermBuilder.DF.var(programVariable);
         }
      }

      public ProgramVariable getProgramVariable() {
         return programVariable;
      }

      public Term getSelectParentTerm() {
         return selectParentTerm;
      }

      public Term getSelectValueTerm() {
         return selectValueTerm;
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
         return programVariable + (selectParentTerm != null ? " of " + selectParentTerm : "") + " is " + selectValueTerm;
      }
   }
   
   protected static class ExecutionVariableValuePair {
      private IProgramVariable programVariable;
      private Term parent;
      private Term value;

      public ExecutionVariableValuePair(IProgramVariable programVariable, Term parent, Term value) {
         assert programVariable != null;
         assert value != null;
         this.programVariable = programVariable;
         this.parent = parent;
         this.value = value;
      }

      public IProgramVariable getProgramVariable() {
         return programVariable;
      }

      public Term getParent() {
         return parent;
      }

      public Term getValue() {
         return value;
      }

      @Override
      public boolean equals(Object obj) {
         if (obj instanceof ExecutionVariableValuePair) {
            ExecutionVariableValuePair other = (ExecutionVariableValuePair)obj;
            return getProgramVariable().equals(other.getProgramVariable()) &&
                   getParent() != null ? getParent().equals(other.getParent()) : other.getParent() == null &&
                   getValue().equals(other.getValue());
         }
         else {
            return false;
         }
      }

      @Override
      public int hashCode() {
         return getProgramVariable().hashCode() + 
                (getParent() != null ? getParent().hashCode() : 0) +
                getValue().hashCode();
      }

      @Override
      public String toString() {
         return getProgramVariable() +
                (getParent() != null ? " of " + getParent() : "") +
                " is " + getValue();
      }
   }
}
