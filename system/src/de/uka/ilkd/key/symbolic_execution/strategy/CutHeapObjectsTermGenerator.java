package de.uka.ilkd.key.symbolic_execution.strategy;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;

/**
 * This {@link TermGenerator} is used by the {@link SymbolicExecutionStrategy}
 * to add early alias checks of used objects as target of store operations
 * on heaps. To achieve this, this {@link TermGenerator} generates equality
 * {@link Term}s for each possible combination of objects.
 * @author Martin Hentschel
 */
public class CutHeapObjectsTermGenerator implements TermGenerator {
   /**
    * {@inheritDoc}
    */
   @Override
   public Iterator<Term> generate(RuleApp app, PosInOccurrence pos, Goal goal) {
      // Compute collect terms of sequent formulas
      Sequent sequent = goal.sequent();
      Set<Term> topTerms = new HashSet<Term>();
      for (SequentFormula sf : sequent) {
         topTerms.add(sf.formula());
      }
      // Compute equality terms
      HeapLDT heapLDT = goal.node().proof().getServices().getTypeConverter().getHeapLDT();
      Set<Term> equalityTerms = new LinkedHashSet<Term>();
      for (SequentFormula sf : sequent) {
         collectEqualityTerms(sf, equalityTerms, topTerms, heapLDT);
      }
      return equalityTerms.iterator();
   }
   
   /**
    * Computes all possible equality terms between objects in the given {@link SequentFormula}.
    * @param sf The {@link SequentFormula} to work with.
    * @param equalityTerms The result {@link Set} with the equality {@link Term}s to fill.
    * @param topTerms The terms of all sequent formulas
    * @param heapLDT The {@link HeapLDT} to use.
    */
   protected void collectEqualityTerms(SequentFormula sf, Set<Term> equalityTerms, Set<Term> topTerms, HeapLDT heapLDT) {
      // Collect objects (target of store operations on heap)
      Set<Term> storeLocations = new LinkedHashSet<Term>();
      collectStoreLocations(sf.formula(), storeLocations, heapLDT);
      // Check if equality checks are possible
      if (storeLocations.size() >= 2) {
         // Generate all possible equality checks
         Term[] storeLocationsArray = storeLocations.toArray(new Term[storeLocations.size()]);
         for (int i = 0; i < storeLocationsArray.length; i++) {
            for (int j = i + 1; j < storeLocationsArray.length; j++) {
               Term equality = TermBuilder.DF.equals(storeLocationsArray[i], storeLocationsArray[j]);
               if (!topTerms.contains(equality)) {
                  Term negatedEquality = TermBuilder.DF.not(equality); // The not is because the order of the branches is nicer (assumption: default case that objects are different is shown in symbolic execution trees on the left)
                  if (!topTerms.contains(negatedEquality)) {
                     equalityTerms.add(negatedEquality); // Do equality cut only if knowledge is not already part of the sequent
                  }
               }
            }
         }
      }
   }

   /**
    * Collects recursive all possible targets of store operations on a heap.
    * @param term The {@link Term} to start search in.
    * @param storeLocations The result {@link Set} to fill.
    * @param heapLDT The {@link HeapLDT} to use (it provides the store and create {@link Function}).
    */
   protected void collectStoreLocations(Term term, final Set<Term> storeLocations, final HeapLDT heapLDT) {
      term.execPreOrder(new DefaultVisitor() {
         @Override
         public void visit(Term visited) {
            if (visited.op() == heapLDT.getStore()) {
               storeLocations.add(visited.sub(1));
            }
         }
      });
   }
}
