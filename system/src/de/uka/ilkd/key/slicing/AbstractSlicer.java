package de.uka.ilkd.key.slicing;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.ThisReference;
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
import de.uka.ilkd.key.symbolic_execution.util.IFilter;
import de.uka.ilkd.key.symbolic_execution.util.JavaUtil;
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
    * Computes the aliases specified by the updates of the current {@link Node}
    * at the application {@link PosInOccurrence} and computes the current {@code this} reference.
    * @param node The {@link Node} to analyze.
    * @return A {@link Pair} with the computed alias map and the {@code this} reference or {@code null} if the application {@link PosInOccurrence} is not of interest.
    */
   protected Pair<Map<ReferencePrefix, SortedSet<ReferencePrefix>>, ReferencePrefix> analyzeSequent(Node node) {
      PosInOccurrence pio = node.getAppliedRuleApp().posInOccurrence();
      Term topLevel = pio.constrainedFormula().formula();
      Pair<ImmutableList<Term>,Term> pair = TermBuilder.goBelowUpdates2(topLevel);
      Term modalityTerm = pair.second;
      SymbolicExecutionTermLabel label = SymbolicExecutionUtil.getSymbolicExecutionLabel(modalityTerm);
      Services services = node.proof().getServices();
      HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
      if (label != null) {
         // Solve this reference
         IExecutionContext ec = JavaTools.getInnermostExecutionContext(modalityTerm.javaBlock(), services);
         ReferencePrefix thisReference = ec != null ? ec.getRuntimeInstance() : null;
         // Compute aliases
         Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases = new HashMap<ReferencePrefix, SortedSet<ReferencePrefix>>();
         analyzeUpdates(pair.first, services, heapLDT, aliases, thisReference);
         return new Pair<Map<ReferencePrefix,SortedSet<ReferencePrefix>>, ReferencePrefix>(aliases, thisReference);
      }
      else {
         return null; // Not the modality of interest.
      }
   }
   
   /**
    * Utility method used by {@link #analyzeSequent(Node)} to analyze the given updates.
    * @param updates The update {@link Term}s to analyze.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} of the {@link Services}.
    * @param aliases The alias {@link Map} to fill.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    */
   protected void analyzeUpdates(ImmutableList<Term> updates, 
                                 Services services, 
                                 HeapLDT heapLDT, 
                                 Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                                 ReferencePrefix thisReference) {
      for (Term update : updates) {
         analyzeUpdate(update, services, heapLDT, aliases, thisReference);
      }
   }
   
   /**
    * Recursive utility method used by {@link #analyzeUpdates(ImmutableList, Services, HeapLDT, Map)} to analyze a given update.
    * @param term The update {@link Term} to analyze.
    * @param services The {@link Services} to use.
    * @param heapLDT The {@link HeapLDT} of the {@link Services}.
    * @param aliases The alias {@link Map} to fill.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    */
   protected void analyzeUpdate(Term term, 
                                Services services, 
                                HeapLDT heapLDT, 
                                Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases, 
                                ReferencePrefix thisReference) {
      if (term.op() == UpdateJunctor.PARALLEL_UPDATE) {
         for (int i = 0 ; i < term.arity(); i++) {
            analyzeUpdate(term.sub(i), services, heapLDT, aliases, thisReference);
         }
      }
      else if (term.op() instanceof ElementaryUpdate) {
         UpdateableOperator target = ((ElementaryUpdate) term.op()).lhs();
         if (SymbolicExecutionUtil.isHeap(target, heapLDT)) {
            analyzeHeapUpdate(term.sub(0), services, heapLDT, aliases, thisReference);
         }
         else {
            ReferencePrefix source = toSourceElement(services, term.sub(0));
            if (target instanceof ReferencePrefix && source != null) {
               updateAliases((ReferencePrefix) target, source, aliases ,thisReference);
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
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    */
   protected void analyzeHeapUpdate(Term term, 
                                    Services services, 
                                    HeapLDT heapLDT, 
                                    Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                                    ReferencePrefix thisReference) {
      final Function store = heapLDT.getStore();
      final Function create = heapLDT.getCreate();
      if (term.op() == store) {
         // Analyze parent heap
         analyzeHeapUpdate(term.sub(0), services, heapLDT, aliases, thisReference);
         // Check for alias in current store
         if (SymbolicExecutionUtil.hasReferenceSort(services, term.sub(3))) {
            ReferencePrefix source = toSourceElement(services, term.sub(3));
            if (source != null) {
               ReferencePrefix targetPrefix = toSourceElement(services, term.sub(1));
               ReferencePrefix targetVariable = toSourceElement(services, term.sub(2));
               assert targetVariable instanceof ProgramVariable;
               updateAliases(new FieldReference((ProgramVariable) targetVariable, targetPrefix), source, aliases, thisReference);
            }
         }
      }
      else if (term.op() == create) {
         // Analyze parent heap
         analyzeHeapUpdate(term.sub(0), services, heapLDT, aliases, thisReference);
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
    * If required, all participating entries in the {@link Map} are updated to ensure consistency.
    * @param first The first alias.
    * @param second The second alias.
    * @param aliases The alias {@link Map} to update.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    */
   protected void updateAliases(ReferencePrefix first, 
                                ReferencePrefix second, 
                                Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                                ReferencePrefix thisReference) {
      // Ensure normal form
      first = normalForm(first, thisReference);
      second = normalForm(second, thisReference);
      // Try to get Set for key
      SortedSet<ReferencePrefix> firstValues = aliases.get(first);
      SortedSet<ReferencePrefix> secondValues = aliases.get(second);
      SortedSet<ReferencePrefix> values = null;
      if (firstValues == null && secondValues == null) {
         values = createSortedSet();
         aliases.put(first, values);
         aliases.put(second, values);
      }
      else if (firstValues != null && secondValues == null) {
         values = firstValues;
         aliases.put(second, values);
      }
      else if (firstValues == null && secondValues != null) {
         values = secondValues;
         aliases.put(first, values);
      }
      else if (firstValues != null && secondValues != null) { // both are not null
         values = firstValues;
         for (ReferencePrefix existingPrefix : secondValues) {
            aliases.put(existingPrefix, values);
         }
         values.addAll(secondValues);
      }
      else {
         throw new IllegalStateException(); // Can not happen!
      }
      values.add(first);
      values.add(second);
   }

   /**
    * Ensures that the {@link ReferencePrefix} is in the normal from which
    * means that static variables are directly accessed without a {@link FieldReference}.
    * @param prefix The {@link ReferencePrefix} to check.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @return The {@link ReferencePrefix} in normal form.
    */
   protected ReferencePrefix normalForm(ReferencePrefix prefix, ReferencePrefix thisReference) {
      if (prefix instanceof FieldReference) {
         FieldReference fr = (FieldReference) prefix;
         if (fr.getReferencePrefix() == null) {
            return fr.getProgramVariable();
         }
         else {
            return new FieldReference(fr.getProgramVariable(), normalForm(fr.getReferencePrefix(), thisReference));
         }
      }
      else if (prefix instanceof ProgramVariable) {
         return prefix;
      }
      else if (prefix instanceof ThisReference) {
         return normalForm(thisReference, thisReference);
      }
      else {
         throw new IllegalStateException();
      }
   }
   
   /**
    * Creates a {@link SortedSet} which ensures that the elements are sorted.
    * @return The new created {@link SortedSet}.
    */
   protected SortedSet<ReferencePrefix> createSortedSet() {
      return new TreeSet<ReferencePrefix>(new Comparator<ReferencePrefix>() {
         /**
          * {@inheritDoc}
          */
         @Override
         public int compare(ReferencePrefix o1, ReferencePrefix o2) {
            String o1string = o1.toString();
            String o2string = o2.toString();
            int o1DotCount = JavaUtil.count(o1string, '.');
            int o2DotCount = JavaUtil.count(o2string, '.');
            if (o1DotCount < o2DotCount) {
               return 1;
            }
            else if (o1DotCount > o2DotCount) {
               return -1;
            }
            else {
               return o1string.compareTo(o2string);
            }
         }
      }); // Order is important for normalization;
   }
   
   /**
    * Returns the representative alias for the given {@link ReferencePrefix}.
    * @param referencePrefix The {@link ReferencePrefix}.
    * @param aliases The available aliases.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @return The representative alias.
    */
   protected ReferencePrefix normalizeAlias(ReferencePrefix referencePrefix, 
                                            Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                                            ReferencePrefix thisReference) {
      if (referencePrefix instanceof ProgramVariable) {
         return normalizeAlias((ProgramVariable) referencePrefix, aliases);
      }
      else if (referencePrefix instanceof FieldReference) {
         ImmutableList<ProgramVariable> vars = extractProgramVariables((FieldReference) referencePrefix, thisReference);
         Iterator<ProgramVariable> iter = vars.iterator();
         ProgramVariable next = iter.next();
         ReferencePrefix root = normalizeAlias(next, aliases);
         if (next != root) {
            root = normalizeAlias(root, aliases, thisReference);
         }
         while (iter.hasNext()) {
            next = iter.next();
            root = new FieldReference(next, root);
         }
         return root;
      }
      else if (referencePrefix instanceof ThisReference) {
         return normalizeAlias(thisReference, aliases, thisReference);
      }
      else {
         throw new IllegalStateException();
      }
   }
   
   /**
    * Returns the representative alias of the given {@link ProgramVariable}.
    * @param pv The {@link ProgramVariable}.
    * @param aliases The available aliases.
    * @return The representative alias.
    */
   protected ReferencePrefix normalizeAlias(ProgramVariable pv, 
                                            Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases) {
      Set<ReferencePrefix> alternatives = aliases.get(pv);
      if (alternatives != null) {
         return alternatives.iterator().next(); // Return first alternative
      }
      else {
         return pv;
      }
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
    * If it is contained, the element will be removed.
    * @param sourceElement The {@link SourceElement} to check.
    * @param relevantLocations The {@link Set} with locations of interest.
    * @param aliases The alias {@link Map}.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @return {@code true} is relevant and was removed, {@code false} is not relevant and nothing has changed.
    */
   protected boolean removeRelevant(ReferencePrefix sourceElement, 
                                Set<ReferencePrefix> relevantLocations, 
                                Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases,
                                ReferencePrefix thisReference) {
      ReferencePrefix normalized = normalizeAlias(sourceElement, aliases, thisReference);
      boolean relevant = false;
      Iterator<ReferencePrefix> iterator = relevantLocations.iterator();
      while (!relevant && iterator.hasNext()) {
         ReferencePrefix next = iterator.next();
         ReferencePrefix nextNormalized = normalizeAlias(next, aliases, thisReference);
         if (normalized.equals(nextNormalized)) {
            iterator.remove();
            relevant = true;
         }
      }
      return relevant;
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
                                         Map<ReferencePrefix, SortedSet<ReferencePrefix>> aliases) {
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
    * Extracts all {@link ProgramVariable}s in the given {@link ReferencePrefix}.
    * @param prefix The {@link ReferencePrefix} to work with.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @return An {@link ImmutableList} containing all {@link ProgramVariable}s of the {@link ReferencePrefix} in the order of access.
    */
   protected ImmutableList<ProgramVariable> extractProgramVariables(ReferencePrefix prefix, 
                                                                    ReferencePrefix thisReference) {
      if (prefix instanceof ProgramVariable) {
         return ImmutableSLList.<ProgramVariable>nil().prepend((ProgramVariable) prefix);
      }
      else if (prefix instanceof FieldReference) {
         return extractProgramVariables((FieldReference) prefix, thisReference);
      }
      else {
         throw new IllegalStateException();
      }
   }

   /**
    * Extracts all {@link ProgramVariable}s in the given {@link FieldReference}.
    * @param fr The {@link FieldReference} to work with.
    * @param thisReference The {@link ReferencePrefix} which is represented by {@code this} ({@link ThisReference}).
    * @return An {@link ImmutableList} containing all {@link ProgramVariable}s of the {@link FieldReference} in the order of access.
    */
   protected ImmutableList<ProgramVariable> extractProgramVariables(FieldReference fr, 
                                                                    ReferencePrefix thisReference) {
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
         else if (prefix instanceof ThisReference) {
            if (thisReference instanceof ProgramVariable) {
               result = result.prepend((ProgramVariable) thisReference);
               fr = null;
            }
            else if (thisReference instanceof FieldReference) {
               fr = (FieldReference) thisReference;
            }
            else {
               throw new IllegalStateException();
            }
         }
         else if (prefix == null) {
            fr = null;
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
   protected FieldReference createFieldReference(ReferencePrefix root, 
                                                 ImmutableList<ProgramVariable> variables) {
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

   /**
    * Returns the first found alternative which is still valid.
    * @param oldAlternatives The old alternatives.
    * @param newAlternatives The new alternatives.
    * @return The found alternative or {@code null} if not available.
    */
   protected ReferencePrefix findNewAlternative(final SortedSet<ReferencePrefix> oldAlternatives, 
                                                final SortedSet<ReferencePrefix> newAlternatives) {
      return JavaUtil.search(oldAlternatives, new IFilter<ReferencePrefix>() {
         @Override
         public boolean select(ReferencePrefix element) {
            return !newAlternatives.contains(element);
         }
      });
   }

   /**
    * Computes the length of a common prefix.
    * @param candidates The possible candidates.
    * @param toCheck The {@link ImmutableList} to check.
    * @return The common prefix length which is {@code 0} if no elements are common.
    */
   public static <T> int computeFirstCommonPrefixLength(ImmutableList<ImmutableList<T>> candidates, 
                                                        ImmutableList<T> toCheck) {
      int commonLength = 0;
      Iterator<ImmutableList<T>> iter = candidates.iterator();
      while (commonLength < 1 && iter.hasNext()) {
         ImmutableList<T> next = iter.next();
         if (startsWith(toCheck, next)) {
            commonLength = next.size();
         }
      }
      return commonLength;
   }

   /**
    * Checks if the given {@link ImmutableList} starts with the given prefix.
    * @param list The {@link List} to check.
    * @param prefix The prefix to check.
    * @return {@code true} the first elements in the {@link ImmutableList} are the prefix, {@code false} if the first elements are not equal to the prefix.
    */
   public static <T> boolean startsWith(ImmutableList<T> list, ImmutableList<T> prefix) {
      if (list.size() >= prefix.size()) {
         Iterator<T> listIter = list.iterator();
         Iterator<T> prefixIter = prefix.iterator();
         boolean same = true;
         while (same && prefixIter.hasNext()) {
            T listNext = listIter.next();
            T prefixNext = prefixIter.next();
            if (!JavaUtil.equals(listNext, prefixNext)) {
               same = false;
            }
         }
         return same;
      }
      else {
         return false;
      }
   }
}
