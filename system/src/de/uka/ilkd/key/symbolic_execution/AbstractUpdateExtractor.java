package de.uka.ilkd.key.symbolic_execution;

import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicLayout;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Provides the basic functionality to extract values from updates.
 * @author Martin Hentschel
 */
public abstract class AbstractUpdateExtractor {
   /**
    * Contains the {@link Node} of KeY's proof tree to compute memory layouts for.
    */
   protected final Node node;
   
   /**
    * The {@link PosInOccurrence} of the modality or its updates.
    */
   protected final PosInOccurrence modalityPio;
   
   /**
    * An incremented number used to give each pre value an unique name.
    */
   private int preVariableIndex = 0;

   /**
    * Constructor.
    * @param node The {@link Node} of KeY's proof tree to compute memory layouts for.
    * @param modalityPio The {@link PosInOccurrence} of the modality or its updates.
    */
   public AbstractUpdateExtractor(Node node, 
                                  PosInOccurrence modalityPio) {
      assert node != null;
      assert modalityPio != null;
      this.node = node;
      this.modalityPio = modalityPio;
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
      // Go up in parent hierarchy and collect updates on all update applications
      PosInOccurrence pio = modalityPio;
      while (pio != null) {
         Term updateApplication = pio.subTerm();
         if (updateApplication.op() == UpdateApplication.UPDATE_APPLICATION) {
            Term topUpdate = UpdateApplication.getUpdate(updateApplication);
            collectLocationsFromTerm(topUpdate, locationsToFill, updateCreatedObjectsToFill, updateValueObjectsToFill, objectsToIgnore);
         }
         if (!pio.isTopLevel()) {
            pio = pio.up();
         }
         else {
            pio = null;
         }
      }
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
               Term arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, selectArgument.sub(2));
               if (arrayIndex != null) {
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
            Term arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, term.sub(2));
            if (arrayIndex != null) {
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
      for (SequentFormula sf : sequent) {
         result.addAll(extractLocationsFromTerm(sf.formula(), objectsToIgnore));
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
                  Term arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, term.sub(2));
                  if (arrayIndex != null) {
                     if (selectTerm.op() instanceof ProgramVariable) {
                        toFill.add(new ExtractLocationParameter((ProgramVariable)selectTerm.op(), true));
                     }
                     toFill.add(new ExtractLocationParameter(arrayIndex, selectTerm));
                  }
                  else {
                     // Nothing to do, since program variable and array index is undefined.
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
      private final ProgramVariable programVariable;
      
      /**
       * The array index or {@code null} if a {@link ProgramVariable} is used instead.
       */
      private final Term arrayIndex;
      
      /**
       * An optional parent object represented as {@link Term}. If it is {@code null} an {@link IProgramVariable} of the state is represented.
       */
      private final Term parentTerm;
      
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
      private final LocationVariable preVariable;
      
      /**
       * Defines if this location should explicitly be shown on the state.
       */
      private final boolean stateMember;

      /**
       * Constructor.
       * @param programVariable The {@link ProgramVariable}.
       * @param stateMember Defines if this location should explicitly be shown on the state.
       * @throws ProofInputException Occurred Exception.
       */
      public ExtractLocationParameter(ProgramVariable programVariable, 
                                      boolean stateMember) throws ProofInputException {
         this(programVariable, null, stateMember);
      }

      /**
       * Constructor.
       * @param programVariable The {@link ProgramVariable}.
       * @param parentTerm The parent object represented as {@link Term}.
       * @throws ProofInputException Occurred Exception.
       */
      public ExtractLocationParameter(ProgramVariable programVariable, 
                                      Term parentTerm) throws ProofInputException {
         this(programVariable, parentTerm, false);
      }
      
      /**
       * Constructor.
       * @param programVariable The {@link ProgramVariable}.
       * @param parentTerm The parent object represented as {@link Term}.
       * @param stateMember Defines if this location should explicitly be shown on the state.
       * @throws ProofInputException Occurred Exception.
       */
      protected ExtractLocationParameter(ProgramVariable programVariable, 
                                         Term parentTerm,
                                         boolean stateMember) throws ProofInputException {
         assert programVariable != null;
         this.programVariable = programVariable;
         this.parentTerm = parentTerm;
         this.preVariable = createLocationVariable("Pre" + preVariableIndex++, parentTerm != null ? parentTerm.sort() : programVariable.sort());
         this.arrayIndex = null;
         this.stateMember = stateMember;
      }
      
      /**
       * Constructor.
       * @param arrayIndex The array index.
       * @param parentTerm The parent object represented as {@link Term}.
       * @throws ProofInputException Occurred Exception.
       */
      public ExtractLocationParameter(Term arrayIndex, 
                                      Term parentTerm) throws ProofInputException {
         assert parentTerm != null;
         this.programVariable = null;
         this.arrayIndex = arrayIndex;
         this.parentTerm = parentTerm;
         this.preVariable = createLocationVariable("Pre" + preVariableIndex++, parentTerm.sort());
         this.stateMember = false;
      }

      /**
       * Creates a new {@link LocationVariable} with the given name and {@link Sort}.
       * @param name The name of the new variable.
       * @param sort The {@link Sort} of the new variable.
       * @return The created {@link LocationVariable}.
       * @throws ProofInputException Occurred Exception.
       */
      protected LocationVariable createLocationVariable(String name, Sort sort) throws ProofInputException {
         return new LocationVariable(new ProgramElementName(name), sort);
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
         return arrayIndex != null;
      }
      
      /**
       * Returns the array index.
       * @return The array index.
       */
      public Term getArrayIndex() {
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
               return getServices().getTermBuilder().dotArr(parentTerm, arrayIndex);
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
            return JavaUtil.equals(arrayIndex, other.arrayIndex) &&
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
         result = 31 * result + (arrayIndex != null ? arrayIndex.hashCode() : 0);
         result = 31 * result + (stateMember ? 1 : 0);
         result = 31 * result + (parentTerm != null ? parentTerm.hashCode() : 0);
         result = 31 * result + (programVariable != null ? programVariable.hashCode() : 0);
         return result;
      }
   }
   
   /**
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
    * @param layoutCondition An optional condition to consider.
    * @param layoutTerm The result term to use in side proof.
    * @param locations The locations to compute in side proof.
    * @param currentLayout {@code true} current layout, {@code false} initial layout.
    * @return The computed {@link ExecutionVariableValuePair}s.
    * @throws ProofInputException Occurred Exception.
    */
   protected Set<ExecutionVariableValuePair> computeVariableValuePairs(Term layoutCondition,
                                                                       Term layoutTerm, 
                                                                       Set<ExtractLocationParameter> locations,
                                                                       boolean currentLayout) throws ProofInputException {
      // Get original updates
      ImmutableList<Term> originalUpdates;
      if (!currentLayout) {
         originalUpdates = ImmutableSLList.nil();
      }
      else {
         Term originalModifiedFormula = modalityPio.constrainedFormula().formula();
         originalUpdates = TermBuilder.goBelowUpdates2(originalModifiedFormula).first;            
      }
      // Combine memory layout with original updates
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
      Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, modalityPio, layoutCondition, layoutTerm, newUpdates, false);
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
               Term value = resultTerm.sub(param.getValueTermIndexInStatePredicate());
               value = SymbolicExecutionUtil.replaceSkolemConstants(goal.sequent(), value, getServices());
               if (param.isArrayIndex()) {
                  pair = new ExecutionVariableValuePair(param.getArrayIndex(), param.getParentTerm(), value, condition, param.isStateMember());
               }
               else {
                  pair = new ExecutionVariableValuePair(param.getProgramVariable(), param.getParentTerm(), value, condition, param.isStateMember());
               }
               pairs.add(pair);
            }
         }
         return pairs;
      }
      finally {
         SideProofUtil.disposeOrStore("Layout computation on node " + node.serialNr() + " with layout term " + ProofSaver.printAnything(layoutTerm, getServices()) + ".", info);
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
      private final ProgramVariable programVariable;

      /**
       * The array index or {@code null} if a {@link ProgramVariable} is used instead.
       */
      private final Term arrayIndex;
      
      /**
       * An optional parent object or {@code null} if it is a value/association of the state.
       */
      private final Term parent;
      
      /**
       * The value or association target.
       */
      private final Term value;
      
      /**
       * Defines if this location should explicitly be shown on the state.
       */
      private final boolean stateMember;
      
      /**
       * An optional condition under which the value is valid.
       */
      private final Term condition;

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
         this.arrayIndex = null;
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
      public ExecutionVariableValuePair(Term arrayIndex, 
                                        Term parent, 
                                        Term value, 
                                        Term condition,
                                        boolean stateMember) {
         assert parent != null;
         assert value != null;
         this.programVariable = null;
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
         return arrayIndex != null;
      }

      /**
       * Returns the array index.
       * @return The array index.
       */
      public Term getArrayIndex() {
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
            return isArrayIndex() ? getArrayIndex().equals(other.getArrayIndex()) : getProgramVariable().equals(other.getProgramVariable()) &&
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
         result = 31 * result + (isArrayIndex() ? getArrayIndex().hashCode() : getProgramVariable().hashCode());
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
                   " is " + getValue() + (getCondition() != null ? " under condition " + getCondition() : "");
         }
         else {
            return getProgramVariable() +
                   (getParent() != null ? " of " + getParent() : "") +
                   " is " + getValue() + (getCondition() != null ? " under condition " + getCondition() : "");
         }
      }
   }
}
