package de.uka.ilkd.key.symbolic_execution;

import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
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
               if (!isImplicitProgramVariable(var) && 
                   !objectsToIgnore.contains(getServices().getTermBuilder().var(var)) &&
                   !hasFreeVariables(updateTerm)) {
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
               if (!isImplicitProgramVariable(var) && 
                   !hasFreeVariables(selectArgument.sub(2))) {
                  locationsToFill.add(new ExtractLocationParameter(var, selectArgument.sub(1)));
               }
            }
            else {
               Term arrayIndex = SymbolicExecutionUtil.getArrayIndex(getServices(), heapLDT, selectArgument.sub(2));
               if (arrayIndex != null) {
                  if (!hasFreeVariables(arrayIndex)) {
                     locationsToFill.add(new ExtractLocationParameter(arrayIndex, selectArgument.sub(1)));
                  }
               }
               else {
                  throw new ProofInputException("Unsupported select statement \"" + term + "\".");
               }
            }
         }
         else if (selectArgument.op() instanceof IProgramVariable) {
            ProgramVariable var = (ProgramVariable)selectArgument.op();
            if (!isImplicitProgramVariable(var) && 
                !hasFreeVariables(selectArgument)) {
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
            if (!isImplicitProgramVariable(var) && !hasFreeVariables(term.sub(2))) {
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
            if (arrayIndex != null && !hasFreeVariables(arrayIndex)) {
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
    * Checks if the given {@link Term} has free variables.
    * @param term The {@link Term} to check.
    * @return {@code true} has free variables, {@code false} does not have free variables.
    */
   protected boolean hasFreeVariables(Term term) {
      return term != null && !term.freeVars().isEmpty();
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
             !objectsToIgnore.contains(term) &&
             !hasFreeVariables(term)) {
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
                  if (!isImplicitProgramVariable(var) &&
                      !hasFreeVariables(term.sub(2))) {
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
                  if (arrayIndex != null && !hasFreeVariables(arrayIndex)) {
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
            if (!objectsToIgnore.contains(term.sub(0)) &&
                !hasFreeVariables(term)) {
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
      final ProofEnvironment sideProofEnv = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(getProof(), true); // New OneStepSimplifier is required because it has an internal state and the default instance can't be used parallel.
      Sequent sequent = SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, modalityPio, layoutCondition, layoutTerm, newUpdates, false);
      // Instantiate and run proof
      ApplyStrategy.ApplyStrategyInfo info = SideProofUtil.startSideProof(getProof(), 
                                                                          sideProofEnv,
                                                                          sequent, 
                                                                          StrategyProperties.METHOD_CONTRACT,
                                                                          StrategyProperties.LOOP_INVARIANT,
                                                                          StrategyProperties.QUERY_ON,
                                                                          StrategyProperties.SPLITTING_NORMAL);
      try {
         @SuppressWarnings("unchecked")
         Map<Term, Set<Goal>>[] paramValueMap = new Map[locations.size()];
         // Group equal values as precondition of computeValueConditions(...)
         for (Goal goal : info.getProof().openGoals()) {
            Term resultTerm = SideProofUtil.extractOperatorTerm(goal, layoutTerm.op());
            int i = 0;
            for (ExtractLocationParameter param : locations) {
               Map<Term, Set<Goal>> valueMap = paramValueMap[i];
               if (valueMap == null) {
                  valueMap = new LinkedHashMap<Term, Set<Goal>>();
                  paramValueMap[i] = valueMap;
               }
               Term value = resultTerm.sub(param.getValueTermIndexInStatePredicate());
               value = SymbolicExecutionUtil.replaceSkolemConstants(goal.sequent(), value, getServices());
               Set<Goal> valueList = valueMap.get(value);
               if (valueList == null) {
                  valueList = new LinkedHashSet<Goal>();
                  valueMap.put(value, valueList);
               }
               valueList.add(goal);
               i++;
            }
         }
         // Compute values including conditions
         Map<Node, Term> branchConditionCache = new HashMap<Node, Term>();
         Set<ExecutionVariableValuePair> pairs = new LinkedHashSet<ExecutionVariableValuePair>();
         int i = 0;
         for (ExtractLocationParameter param : locations) {
            for (Entry<Term, Set<Goal>> valueEntry : paramValueMap[i].entrySet()) {
               Map<Goal, Term> conditionsMap = computeValueConditions(valueEntry.getValue(), branchConditionCache);
               if (param.isArrayIndex()) {
                  for (Goal goal : valueEntry.getValue()) {
                     ExecutionVariableValuePair pair = new ExecutionVariableValuePair(param.getArrayIndex(), param.getParentTerm(), valueEntry.getKey(), conditionsMap.get(goal), param.isStateMember(), goal.node());
                     pairs.add(pair);
                  }
               }
               else {
                  for (Goal goal : valueEntry.getValue()) {
                     ExecutionVariableValuePair pair = new ExecutionVariableValuePair(param.getProgramVariable(), param.getParentTerm(), valueEntry.getKey(), conditionsMap.get(goal), param.isStateMember(), goal.node());
                     pairs.add(pair);
                  }
               }
            }
            i++;
         }
         return pairs;
      }
      finally {
         SideProofUtil.disposeOrStore("Layout computation on node " + node.serialNr() + " with layout term " + ProofSaver.printAnything(layoutTerm, getServices()) + ".", info);
      }
   }
   
   /**
    * This method computes for all given {@link Goal}s representing the same 
    * value their path conditions. A computed path condition will consists only
    * of the branch conditions which contribute to the value. Branch conditions
    * of splits which does not contribute to the value are ignored.
    * <p>
    * The implemented algorithm works as follows:
    * <ol>
    *    <li>
    *       The given {@link Goal}s have to be all {@link Goal}s of the side 
    *       proof providing the same value. This means that other branches/goals 
    *       of the side proof result in different branches.
    *    </li>
    *    <li>
    *       A backward iteration on the parent {@link Node}s starting at the 
    *       {@link Goal}s is performed until the first parent with at least
    *       two open children has been found.
    *       The iteration is only performed on one
    *       goal (or the {@link Node} it stops last) at a time. The iteration
    *       is always performed on the {@link Node} with the highest serial
    *       number to ensure that different {@link Goal} will meet at their
    *       common parents.
    *    </li>
    *    <li>
    *       When the iteration of all children of a {@link Node} has met,
    *       the branch conditions are computed if the split contributes to
    *       the value. 
    *       A split contributes to a value if at least one branch is not
    *       reached by backward iteration meaning that its {@link Goal}s
    *       provide different values.
    *    </li>
    *    <li>The backward iteration ends when the root is reached.</li>
    *    <li>
    *       Finally, for each {@link Goal} is the path condition computed.
    *       The path condition is the conjunction over all found branch 
    *       conditions contributing to the value.
    *    </li>
    * </ol>
    * @param valueGoals All {@link Goal}s of the side proof which provide the same value (result).
    * @param branchConditionCache A cache of already computed branch conditions.
    * @return A {@link Map} which contains for each {@link Goal} the computed path condition consisting of only required splits.
    * @throws ProofInputException Occurred Exception
    */
   protected Map<Goal, Term> computeValueConditions(Set<Goal> valueGoals, 
                                                    Map<Node, Term> branchConditionCache) throws ProofInputException {
      Comparator<NodeGoal> comparator = new Comparator<NodeGoal>() {
         @Override
         public int compare(NodeGoal o1, NodeGoal o2) {
            return o2.getSerialNr() - o1.getSerialNr(); // Descending order
         }
      };
      // Initialize condition for each goal with true
      Set<Node> untriedRealGoals = new HashSet<Node>();
      Map<Goal, Set<Term>> goalConditions = new HashMap<Goal, Set<Term>>();
      List<NodeGoal> sortedBranchLeafs = new LinkedList<NodeGoal>();
      for (Goal goal : valueGoals) {
         JavaUtil.binaryInsert(sortedBranchLeafs, new NodeGoal(goal), comparator);
         goalConditions.put(goal, new LinkedHashSet<Term>());
         untriedRealGoals.add(goal.node());
      }
      // Compute branch conditions
      List<NodeGoal> waitingBranchLeafs = new LinkedList<NodeGoal>();
      Map<Node, List<NodeGoal>> splitMap = new HashMap<Node, List<NodeGoal>>();
      while (!sortedBranchLeafs.isEmpty()) {
         // Go back to parent with at least two open goals on maximum outer leaf
         NodeGoal maximumOuterLeaf = sortedBranchLeafs.remove(0); // List is sorted in descending order
         NodeGoal childGoal = iterateBackOnParents(maximumOuterLeaf, !untriedRealGoals.remove(maximumOuterLeaf.getCurrentNode()));
         if (childGoal != null) { // Root is not reached
            waitingBranchLeafs.add(childGoal);
            List<NodeGoal> childGoals = splitMap.get(childGoal.getParent());
            if (childGoals == null) {
               childGoals = new LinkedList<NodeGoal>();
               splitMap.put(childGoal.getParent(), childGoals);
            }
            childGoals.add(childGoal);
            // Check if parent is reached on all child nodes
            if (isParentReachedOnAllChildGoals(childGoal.getParent(), sortedBranchLeafs)) {
               // Check if the split contributes to the path condition which is the case if at least one branch is not present (because it has a different value)
               if (childGoals.size() != childGoal.getParent().childrenCount()) {
                  // Add branch condition to conditions of all child goals
                  for (NodeGoal nodeGoal : childGoals) {
                     Term branchCondition = computeBranchCondition(nodeGoal.getCurrentNode(), branchConditionCache);
                     for (Goal goal : nodeGoal.getStartingGoals()) {
                        Set<Term> conditions = goalConditions.get(goal);
                        conditions.add(branchCondition);
                     }
                  }
               }
               // Add waiting NodeGoals to working list
               for (NodeGoal nodeGoal : childGoals) {
                  waitingBranchLeafs.remove(nodeGoal);
                  JavaUtil.binaryInsert(sortedBranchLeafs, nodeGoal, comparator);
               }
            }
         }
      }
      // Compute final condition (redundant path conditions are avoided)
      Map<Goal, Term> pathConditionsMap = new LinkedHashMap<Goal, Term>();
      for (Entry<Goal, Set<Term>> entry : goalConditions.entrySet()) {
         Term pathCondition = getServices().getTermBuilder().and(entry.getValue());
         pathConditionsMap.put(entry.getKey(), pathCondition);
      }
      return pathConditionsMap;
   }

   /**
    * Checks if parent backward iteration on all given {@link NodeGoal} has
    * reached the given {@link Node}.
    * @param currentNode The current {@link Node} to check.
    * @param branchLeafs The {@link NodeGoal} on which backward iteration was performed.
    * @return {@code true} All {@link NodeGoal}s have passed the given {@link Node}, {@code false} if at least one {@link NodeGoal} has not passed the given {@link Node}.
    */
   protected boolean isParentReachedOnAllChildGoals(Node currentNode, List<NodeGoal> branchLeafs) {
      if (!branchLeafs.isEmpty()) {
         return branchLeafs.get(0).getSerialNr() <= currentNode.serialNr();
      }
      else {
         return true;
      }
   }

   /**
    * Performs a backward iteration on the parents starting at the given
    * {@link NodeGoal} until the first parent with at least two open
    * branches has been found.
    * @param nodeToStartAt The {@link NodeGoal} to start parent backward iteration at.
    * @param force {@code true} first parent is not checked, {@code false} also first parent is checked.
    * @return The first found parent with at least two open child branches or {@code null} if the root has been reached.
    */
   protected NodeGoal iterateBackOnParents(NodeGoal nodeToStartAt, boolean force) {
      // Go back to parent with at least two open branches
      Node child = force ? nodeToStartAt.getParent() : nodeToStartAt.getCurrentNode();
      Node parent = child.parent();
      while (parent != null && countOpenChildren(parent) == 1) {
         child = parent;
         parent = child.parent();
      }
      // Store result
      if (parent != null) {
         return new NodeGoal(child, nodeToStartAt.getStartingGoals());
      }
      else {
         return null;
      }
   }
   
   /**
    * Counts the number of open child {@link Node}s.
    * @param node The {@link Node} to count its open children.
    * @return The number of open child {@link Node}s.
    */
   protected int countOpenChildren(Node node) {
      int openChildCount = 0;
      for (int i = 0; i < node.childrenCount(); i++) {
         Node child = node.child(i);
         if (!child.isClosed()) {
            openChildCount++;
         }
      }
      return openChildCount;
   }
   
   /**
    * Utility class used by {@link AbstractUpdateExtractor#computeValueConditions(Set, Map)}.
    * Instances of this class store the current {@link Node} and the {@link Goal}s at which backward iteration on parents has started.
    * @author Martin Hentschel
    */
   protected static class NodeGoal {
      /**
       * The current {@link Node}.
       */
      private final Node currentNode;
      
      /**
       * The {@link Goal}s at which backward iteration has started.
       */
      private final ImmutableList<Goal> startingGoals;

      /**
       * Constructor.
       * @param goal The current {@link Goal} to start backward iteration at.
       */
      public NodeGoal(Goal goal) {
         this(goal.node(), ImmutableSLList.<Goal>nil().prepend(goal));
      }

      /**
       * A reached child node during backward iteration.
       * @param currentNode The current {@link Node}.
       * @param startingGoals The {@link Goal}s at which backward iteration has started.
       */
      public NodeGoal(Node currentNode, ImmutableList<Goal> startingGoals) {
         this.currentNode = currentNode;
         this.startingGoals = startingGoals;
      }

      /**
       * Returns the current {@link Node}.
       * @return The current {@link Node}.
       */
      public Node getCurrentNode() {
         return currentNode;
      }
      
      /**
       * Returns the parent of {@link #getCurrentNode()}.
       * @return The parent of {@link #getCurrentNode()}.
       */
      public Node getParent() {
         return currentNode.parent();
      }

      /**
       * Returns the serial number of {@link #getCurrentNode()}.
       * @return The serial number of {@link #getCurrentNode()}.
       */
      public int getSerialNr() {
         return currentNode.serialNr();
      }

      /**
       * Returns the {@link Goal}s at which backward iteration has started.
       * @return The {@link Goal}s at which backward iteration has started.
       */
      public ImmutableList<Goal> getStartingGoals() {
         return startingGoals;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         StringBuffer sb = new StringBuffer();
         sb.append(currentNode.serialNr());
         sb.append(" starting from goals ");
         boolean afterFirst = false;
         for (Goal goal : startingGoals) {
            if (afterFirst) {
               sb.append(", ");
            }
            else {
               afterFirst = true;
            }
            sb.append(goal.node().serialNr());
         }
         return sb.toString();
      }
   }
   
   /**
    * Computes the branch condition if not already present in the cache
    * and stores it in the cache. If the condition is already present in the 
    * cache it is returned from it.
    * @param node The {@link Node} to compute its branch condition.
    * @param branchConditionCache The cache of already computed branch conditions.
    * @return The computed branch condition.
    * @throws ProofInputException Occurred Exception.
    */
   protected Term computeBranchCondition(Node node, 
                                         Map<Node, Term> branchConditionCache) throws ProofInputException {
      Term result = branchConditionCache.get(node);
      if (result == null) {
         result = SymbolicExecutionUtil.computeBranchCondition(node, true);
         branchConditionCache.put(node, result);
      }
      return result;
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
       * The {@link Node} on which this result is based on.
       */
      private final Node goalNode;

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
                                        boolean stateMember,
                                        Node goalNode) {
         assert programVariable != null;
         assert value != null;
         this.programVariable = programVariable;
         this.parent = parent;
         this.value = value;
         this.condition = condition;
         this.arrayIndex = null;
         this.stateMember = stateMember;
         this.goalNode = goalNode;
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
                                        boolean stateMember,
                                        Node goalNode) {
         assert parent != null;
         assert value != null;
         this.programVariable = null;
         this.arrayIndex = arrayIndex;
         this.parent = parent;
         this.value = value;
         this.condition = condition;
         this.stateMember = stateMember;
         this.goalNode = goalNode;
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
       * Returns the {@link Node} on which this result is based on.
       * @return The {@link Node} on which this result is based on.
       */
      public Node getGoalNode() {
         return goalNode;
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
                   getValue().equals(other.getValue()) &&
                   getGoalNode().equals(other.getGoalNode());
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
         result = 31 * result + getGoalNode().hashCode();
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
                   " is " + getValue() + (getCondition() != null ? " under condition " + getCondition() : "") +
                   " at goal " + goalNode.serialNr();
         }
         else {
            return getProgramVariable() +
                   (getParent() != null ? " of " + getParent() : "") +
                   " is " + getValue() + (getCondition() != null ? " under condition " + getCondition() : "") +
                   " at goal " + goalNode.serialNr();
         }
      }
   }
}
