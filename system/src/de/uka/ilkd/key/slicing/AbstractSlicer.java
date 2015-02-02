package de.uka.ilkd.key.slicing;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.Pair;

/**
 * Defines the basic functionality for slicing algorithms.
 * @author Martin Hentschel
 */
public abstract class AbstractSlicer {
   /**
    * Computes the slice.
    * @param seedNode The seed {@link Node} to start slicing at.
    * @param term The seed {@link Term}.
    * @return The computed slice.
    */
   public ImmutableArray<Node> slice(Node seedNode, Term term) {
      return slice(seedNode, toSourceElement(seedNode.proof().getServices(), term));
   }

   /**
    * Computes the slice.
    * @param seedNode The seed {@link Node} to start slicing at.
    * @param seedLocation The seed {@link ReferencePrefix}.
    * @return The computed slice.
    */
   public ImmutableArray<Node> slice(Node seedNode, ReferencePrefix seedLocation) {
      // Ensure that seed node is valid
      if (seedNode.getAppliedRuleApp() == null) {
         throw new IllegalStateException("No rule applied on seed Node '" + seedNode.serialNr() + "'.");
      }
      PosInOccurrence pio = seedNode.getAppliedRuleApp().posInOccurrence();
      Term topLevel = pio.constrainedFormula().formula();
      Pair<ImmutableList<Term>,Term> pair = TermBuilder.goBelowUpdates2(topLevel);
      Term modalityTerm = pair.second;
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(modalityTerm);
      if (label == null) {
         throw new IllegalStateException("Modality at applied rule does not have the " + SymbolicExecutionTermLabel.NAME + " term label.");
      }
      // Perform slicing
      return doSlicing(seedNode, seedLocation);
   }

   /**
    * Performs the slicing.
    * @param seedNode The seed {@link Node} to start slicing at.
    * @param seedLocation The seed {@link ReferencePrefix}.
    * @return The computed slice.
    */
   protected abstract ImmutableArray<Node> doSlicing(Node seedNode, ReferencePrefix seedLocation);
   
   /**
    * Creates a {@link Map} which contains all available aliases.
    * All aliases refer to the same {@link Set} in the {@link Map} and each
    * entry in a {@link Set} is also used as key in the {@link Map}.
    * @param node The {@link Node} to analyze.
    * @return The created alias {@link Map} or {@code null} if the {@link Node} does not perform the symbolic execution of interest.
    */
   protected Map<ReferencePrefix, Set<ReferencePrefix>> createAliasesMap(Node node) {
      PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
      Term topLevel = pio.constrainedFormula().formula();
      Pair<ImmutableList<Term>,Term> pair = TermBuilder.goBelowUpdates2(topLevel);
      Term modalityTerm = pair.second;
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(modalityTerm);
      Services services = node.proof().getServices();
      HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
      if (label != null) {
         Map<ReferencePrefix, Set<ReferencePrefix>> aliases = new HashMap<ReferencePrefix, Set<ReferencePrefix>>();
         analyzeUpdates(pair.first, services, heapLDT, aliases);
         return aliases;
      }
      else {
         return null; // Not the modality of interest.
      }
   }
   
   /**
    * Utility method used by {@link #createAliasesMap(Node)} to analyze the given updates.
    * @param updates The update {@link Term}s to analyze.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} of the {@link Services}.
    * @param aliases The alias {@link Map} to fill.
    */
   protected void analyzeUpdates(ImmutableList<Term> updates, 
                                 Services services, 
                                 HeapLDT heapLDT, 
                                 Map<ReferencePrefix, Set<ReferencePrefix>> aliases) {
      for (Term update : updates) {
         analyzeUpdate(update, services, heapLDT, aliases);
      }
   }
   
   /**
    * Recursive utility method used by {@link #analyzeUpdates(ImmutableList, Services, HeapLDT, Map)} to analyze a given update.
    * @param term The update {@link Term} to analyze.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} of the {@link Services}.
    * @param aliases The alias {@link Map} to fill.
    */
   protected void analyzeUpdate(Term term, Services services, HeapLDT heapLDT, Map<ReferencePrefix, Set<ReferencePrefix>> aliases) {
      if (term.op() == UpdateJunctor.PARALLEL_UPDATE) {
         for (int i = 0 ; i < term.arity(); i++) {
            analyzeUpdate(term.sub(i), services, heapLDT, aliases);
         }
      }
      else if (term.op() instanceof ElementaryUpdate) {
         UpdateableOperator target = ((ElementaryUpdate) term.op()).lhs();
         if (SymbolicExecutionUtil.isHeap(target, heapLDT)) {
            analyzeHeapUpdate(term.sub(0), services, heapLDT, aliases);
         }
         else {
            ReferencePrefix source = toSourceElement(services, term.sub(0));
            if (target instanceof ReferencePrefix && source != null) {
               addAliases((ReferencePrefix) target, source, aliases);
            }
         }
      }
      else {
         throw new IllegalArgumentException();
      }
   }

   /**
    * Recursive utility method used by {@link #analyzeUpdate(Term, Services, HeapLDT, Map)} to analyze a given update.
    * @param term The heap update {@link Term} to analyze.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} of the {@link Services}.
    * @param aliases The alias {@link Map} to fill.
    */
   protected void analyzeHeapUpdate(Term term, 
                                    Services services, 
                                    HeapLDT heapLDT, 
                                    Map<ReferencePrefix, Set<ReferencePrefix>> aliases) {
      final Function store = heapLDT.getStore();
      final Function create = heapLDT.getCreate();
      if (term.op() == store) {
         // Analyze parent heap
         analyzeHeapUpdate(term.sub(0), services, heapLDT, aliases);
         // Check for alias in current store
         if (SymbolicExecutionUtil.hasReferenceSort(services, term.sub(3))) {
            ReferencePrefix source = toSourceElement(services, term.sub(3));
            if (source != null) {
               ReferencePrefix targetPrefix = toSourceElement(services, term.sub(1));
               ReferencePrefix targetVariable = toSourceElement(services, term.sub(2));
               assert targetVariable instanceof ProgramVariable;
               addAliases(new FieldReference((ProgramVariable) targetVariable, targetPrefix), source, aliases);
            }
         }
      }
      else if (term.op() == create) {
         throw new IllegalStateException();
      }
      else if (term.op() instanceof IProgramVariable) {
         // Nothing to do, root of heap reached.
      }
      else {
         throw new IllegalStateException();
      }
   }

   /**
    * Adds the found alias consisting of first and second {@link ReferencePrefix} to the alias {@link Map}.
    * @param first The first alias.
    * @param second The second alias.
    * @param aliases The alias {@link Map} to update.
    */
   protected void addAliases(ReferencePrefix first, 
                             ReferencePrefix second, 
                             Map<ReferencePrefix, Set<ReferencePrefix>> aliases) {
      // Try to get Set for key
      Set<ReferencePrefix> values = aliases.get(first);
      if (values == null) {
         // Try to get Set for value
         values = aliases.get(second);
         if (values == null) {
            // Create new Set
            values = new HashSet<ReferencePrefix>();
            aliases.put(second, values);
         }
         aliases.put(first, values);
      }
      values.add(first);
      values.add(second);
   }

   /**
    * Computes the {@link ReferencePrefix} of the given {@link SourceElement}.
    * @param sourceElement The {@link SourceElement} to work with.
    * @return The {@link ReferencePrefix} or {@code null} if the {@link SourceElement} can't be represented as {@link ReferencePrefix}.
    */
   protected ReferencePrefix computeReferencePrefix(SourceElement sourceElement) {
      if (sourceElement instanceof PassiveExpression) {
         if (((PassiveExpression) sourceElement).getChildCount() != 1) {
            throw new IllegalStateException();
         }
         sourceElement = ((PassiveExpression) sourceElement).getChildAt(0);
      }
      if (sourceElement instanceof FieldReference) {
         return (FieldReference) sourceElement;
      }
      else if (sourceElement instanceof ProgramVariable) {
         return (ProgramVariable) sourceElement;
      }
      else {
         return null;
      }
   }

   /**
    * Checks if the given {@link SourceElement} is directly or indirectly
    * contained (aliased) in the {@link Set} of relevant locations.
    * @param sourceElement The {@link SourceElement} to check.
    * @param relevantLocations The {@link Set} with locations of interest.
    * @param aliases The alias {@link Map}.
    * @return {@code true} is relevant, {@code false} is not relevant.
    */
   protected boolean isRelevant(SourceElement sourceElement, 
                                Set<ReferencePrefix> relevantLocations, 
                                Map<ReferencePrefix, Set<ReferencePrefix>> aliases) {
      if (sourceElement instanceof IProgramVariable) {
         return relevantLocations.contains(sourceElement);
      }
      else if (sourceElement instanceof FieldReference) {
         // Check current source element for performance reasons
         if (relevantLocations.contains(sourceElement)) {
            return true;
         }
         else {
            // Perform regular field reference check
            FieldReference fr = (FieldReference) sourceElement;
            ReferencePrefix prefix = fr.getReferencePrefix();
            if (prefix == null) { 
               // Static field: Check program variable directly
               return relevantLocations.contains(fr.getProgramVariable());
            }
            else if (prefix instanceof ReferencePrefix) { 
               // Instance field: Check all aliases
               ImmutableList<ProgramVariable> remainingVariables = extractProgramVariables(fr);
               ReferencePrefix root = remainingVariables.head();
               remainingVariables = remainingVariables.tail();
               return checkFieldReference(root, remainingVariables, relevantLocations, aliases);
            }
            else {
               throw new IllegalArgumentException();
            }
         }
      }
      else {
         throw new IllegalArgumentException();
      }
   }
   
   /**
    * Recursive utility method used by {@link #isRelevant(SourceElement, Set, Map)}.
    * @param root The root {@link ReferencePrefix}.
    * @param remainingVariables The remaining {@link ProgramVariable}s in the access path.
    * @param relevantLocations The {@link Set} with locations of interest.
    * @param aliases The alias {@link Map}.
    * @return {@code true} is relevant, {@code false} is not relevant.
    */
   protected boolean checkFieldReference(ReferencePrefix root, 
                                         ImmutableList<ProgramVariable> remainingVariables, 
                                         Set<ReferencePrefix> relevantLocations, 
                                         Map<ReferencePrefix, Set<ReferencePrefix>> aliases) {
      Set<ReferencePrefix> alternatives = aliases.get(root);
      if (alternatives != null) {
         boolean relevant = false;
         Iterator<ReferencePrefix> iterator = alternatives.iterator();
         while (!relevant && iterator.hasNext()) {
            ReferencePrefix alternative = iterator.next();
            FieldReference alternativeFR = createFieldReference(alternative, remainingVariables);
            if (relevantLocations.contains(alternativeFR)) {
               relevant = true;
            }
            else {
               FieldReference childReference = new FieldReference(remainingVariables.head(), alternative);
               relevant = checkFieldReference(childReference, remainingVariables.tail(), relevantLocations, aliases);
            }
         }
         return relevant;
      }
      else {
         return false;
      }
   }

   /**
    * Extracts all {@link ProgramVariable}s in the given {@link FieldReference}.
    * @param fr The {@link FieldReference} to work with.
    * @return An {@link ImmutableList} containing all {@link ProgramVariable}s of the {@link FieldReference} in the order of access.
    */
   protected ImmutableList<ProgramVariable> extractProgramVariables(FieldReference fr) {
      ImmutableList<ProgramVariable> result = ImmutableSLList.nil();
      while (fr != null) {
         result = result.prepend(fr.getProgramVariable());
         ReferencePrefix prefix = fr.getReferencePrefix();
         if (prefix instanceof ProgramVariable) {
            result = result.prepend((ProgramVariable) prefix);
            fr = null;
         }
         else if (prefix instanceof FieldReference) {
            fr = (FieldReference) prefix;
         }
         else {
            throw new IllegalStateException();
         }
      }
      return result;
   }

   /**
    * Creates a new {@link FieldReference} for the given {@link ProgramVariable}s.
    * @param root The root {@link ReferencePrefix}.
    * @param variables The {@link ProgramVariable} to access in order of access.
    * @return The created {@link FieldReference}.
    */
   protected FieldReference createFieldReference(ReferencePrefix root, ImmutableList<ProgramVariable> variables) {
      Iterator<ProgramVariable> iterator = variables.iterator();
      assert iterator.hasNext();
      FieldReference fr = new FieldReference(iterator.next(), root);
      while (iterator.hasNext()) {
         fr = new FieldReference(iterator.next(), fr);
      }
      return fr;
   }
   
   /**
    * Converts the given {@link Term} into a {@link ReferencePrefix}.
    * @param services The {@link Services} to use.
    * @param term The {@link Term} to convert.
    * @return The {@link ReferencePrefix} or {@code null} if the {@link Term} could not be represented as {@link ReferencePrefix}.
    */
   protected ReferencePrefix toSourceElement(Services services, Term term) {
      if (term.op() instanceof ProgramVariable) {
         return (ProgramVariable) term.op();
      }
      else if (SymbolicExecutionUtil.isNullSort(term.sort(), services)) {
         return null;
      }
      else {
         Function selectFunction = services.getTypeConverter().getHeapLDT().getSelect(term.sort(), services);
         if (term.op() == selectFunction) {
            ReferencePrefix prefix = toSourceElement(services, term.sub(1));
            ReferencePrefix variable = toSourceElement(services, term.sub(2));
            assert variable instanceof ProgramVariable;
            return new FieldReference((ProgramVariable) variable, prefix);
         }
         else {
            String name = term.op().name().toString();
            int index = name.toString().indexOf("::");
            if (index >= 0) {
               String fullTypeName = name.substring(0, index);
               String fieldName = name.substring(index + 3);
               ProgramVariable pv = services.getJavaInfo().getAttribute(fullTypeName + "::" + fieldName);
               assert term.op() == services.getTypeConverter().getHeapLDT().getFieldSymbolForPV((LocationVariable) pv, services);
               return pv;
            }
            else {
               return null;
            }
         }
      }
   }
}
