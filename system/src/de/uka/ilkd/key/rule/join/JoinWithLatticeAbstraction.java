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

package de.uka.ilkd.key.rule.join;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.signanalysis.Top;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;

/**
 * Rule that joins two sequents based on a specified set of
 * abstract domain lattices. If no lattice is specified for
 * a given sort, the rule proceeds such that program variables
 * are unchanged if they are equal in both states and applies
 * the if-then-else construction otherwise.
 * 
 * @author Dominic Scheurer
 */
public abstract class JoinWithLatticeAbstraction extends JoinRule {

   /**
    * Returns the abstract domain lattice for the given sort or
    * null if there has no lattice been specified for that sort.
    * 
    * @param s The sort to return the matching lattice for.
    * @param services The services object.
    * @return The abstract domain lattice suitable for the given sort.
    */
   protected abstract AbstractDomainLattice<?> getAbstractDomainForSort(Sort s, Services services);
   
   @Override
   protected SymbolicExecutionState joinStates(
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
         Term programCounter,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
         
      HashSet<LocationVariable> progVars =
            new HashSet<LocationVariable>();
      
      // Collect program variables in Java block
      progVars.addAll(getLocationVariables(programCounter));
      // Collect program variables in update
      progVars.addAll(getUpdateLeftSideLocations(state1.first));
      
      ImmutableList<Term> newElementaryUpdates = ImmutableSLList.nil();
      Term newConstraints = tb.tt();
      
      for (LocationVariable v : progVars) {
         
         Function skolemConstant = null;
         
         Term rightSide1 = getUpdateRightSideFor(state1.first, v);
         Term rightSide2 = getUpdateRightSideFor(state2.first, v);
         
         if (rightSide1 == null) {
            rightSide1 = tb.var(v);
         }
         
         if (rightSide2 == null) {
            rightSide2 = tb.var(v);
         }
         
         AbstractDomainLattice<?> lattice = getAbstractDomainForSort(v.sort(), services);
         Sort heapSort = (Sort) services.getNamespaces().sorts().lookup("Heap");
         
         if (rightSide1.equals(rightSide2)) {
            
            // For equal right sides, we just keep those for
            // preserving idempotency
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        rightSide1));
            
         } else if (v.sort().equals(heapSort)) {
            
            // Heaps are specially joined
            
            Pair<Term, LinkedList<Term>> joinedHeaps =
                  joinHeaps(rightSide1, rightSide2, state1, state2, services);
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        tb.var(v),
                        joinedHeaps.first));
            
            if (joinedHeaps.second.size() > 0) {
               newConstraints = tb.and(newConstraints, tb.and(joinedHeaps.second));
            }
            
         } else if (lattice != null) {
            
            // Join with abstract domain lattice.
            
            AbstractDomainElement abstrElem1 = determineAbstractElem(state1, tb.var(v), lattice, services);
            AbstractDomainElement abstrElem2 = determineAbstractElem(state2, tb.var(v), lattice, services);
            
            AbstractDomainElement joinElem = lattice.join(abstrElem1, abstrElem2);
            
            skolemConstant =
                  getNewScolemConstantForPrefix(joinElem.toString(), v.sort(), services);
            
            newConstraints = tb.and(newConstraints, joinElem.getDefiningAxiom(tb.func(skolemConstant), services));
            //NOTE: We also remember the precise values by if-then-else construction. This
            //      preserves completeness and should also not be harmful to performance in
            //      cases where completeness is also preserved by the lattice. However, if
            //      there are lattices where this construction is bad, it may be safely
            //      removed (no harm to soundness!).
            newConstraints = tb.and(newConstraints, tb.equals(tb.func(skolemConstant),
                  JoinIfThenElse.createIfThenElseTerm(state1, state2, rightSide1, rightSide2, services)));
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        tb.func(skolemConstant)));
            
         } else {
            
            // Apply if-then-else construction
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  JoinIfThenElse.createIfThenElseUpdate(v, state1, state2, services));
            
         }
         
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      // Construct path condition as disjunction
      Term newPathCondition =
            tb.and(
                  createSimplifiedDisjunctivePathCondition(state1.second, state2.second, services),
                  newConstraints);
      
      return new SymbolicExecutionState(newSymbolicState, newPathCondition);
   }
   
   /**
    * Determines the abstract element suitable for the given term.
    * This is accomplished by iterating through the abstract elements
    * (from bottom to top) and trying to verify the corresponding axiom
    * instances.
    * 
    * @param state State in which the evaluation of the defining axioms
    *     should be tested.
    * @param term The term to find an abstract description for.
    * @param lattice The underlying abstract domain.
    * @param services The services object.
    * @return A suitable abstract element for the given location variable.
    */
   private AbstractDomainElement determineAbstractElem(
         SymbolicExecutionState state,
         Term term,
         AbstractDomainLattice<?> lattice,
         Services services) {

      TermBuilder tb = services.getTermBuilder();
      
      Iterator<AbstractDomainElement> it = lattice.iterator();
      while (it.hasNext()) {
         AbstractDomainElement elem = it.next();
         
         Term axiom   = elem.getDefiningAxiom(term, services);
         Term appl    = tb.apply(state.first, axiom);
         Term toProve = tb.imp(state.second, appl);
         
         if (isProvableWithSplitting(toProve, services)) {
            return elem;
         }
      }
      
      return Top.getInstance();
   }
   
   /**
    * Joins two heaps by if-then-else construction. Tries to shift
    * the if-then-else as deeply into the heap as possible.
    * 
    * @param heap1 The first heap term.
    * @param heap2 The second heap term.
    * @param state1 SE state for the first heap term.
    * @param state2 SE state for the second heap term
    * @param services The services object.
    * @return A joined heap term.
    */
   private Pair<Term, LinkedList<Term>> joinHeaps(
         Term heap1,
         Term heap2,
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
         Services services) {
      
      //TODO: Parts of this code appear redundantly in different join rules;
      //      it could be sensible to extract those into an own method.
      
      TermBuilder tb = services.getTermBuilder();      
      LinkedList<Term> newConstraints = new LinkedList<Term>();
      
      if (heap1.equals(heap2)) {
         // Keep equal heaps
         return new Pair<Term, LinkedList<Term>>(heap1, newConstraints);
      }
      
      if (!(heap1.op() instanceof Function) ||
            !(heap2.op() instanceof Function)) {
         // Covers the case of two different symbolic heaps
         return new Pair<Term, LinkedList<Term>>(
               JoinIfThenElse.createIfThenElseTerm(state1, state2, heap1, heap2, services),
               newConstraints);
      }
      
      Function storeFunc = (Function) services.getNamespaces().functions().lookup("store");
      Function createFunc = (Function) services.getNamespaces().functions().lookup("create");
      //Note: Check if there are other functions that should be covered.
      //      Unknown functions are treated by if-then-else procedure.
      
      if (((Function) heap1.op()).equals(storeFunc) &&
            ((Function) heap2.op()).equals(storeFunc)) {
         
         // Store operations.
         
         // Decompose the heap operations.
         Term subHeap1 = heap1.sub(0);
         LocationVariable pointer1 = (LocationVariable) heap1.sub(1).op();
         Function field1 = (Function) heap1.sub(2).op();
         Term value1 = heap1.sub(3);
         
         Term subHeap2 = heap2.sub(0);
         LocationVariable pointer2 = (LocationVariable) heap2.sub(1).op();
         Function field2 = (Function) heap2.sub(2).op();
         Term value2 = heap2.sub(3);
         
         if (pointer1.equals(pointer2) && field1.equals(field2)) {
            // Potential for deep merge: Access of same object / field.
            
            Pair<Term, LinkedList<Term>> joinedSubHeap = joinHeaps(subHeap1, subHeap2, state1, state2, services);
            newConstraints.addAll(joinedSubHeap.second);
            
            Term joinedVal = null;
            AbstractDomainLattice<?> lattice = null;
            
            if (value1.equals(value2)) {
               // Idempotency...
               joinedVal = value1;
               
            } else if ((lattice = getAbstractDomainForSort(((Function) value1.op()).sort(), services)) != null) {
               
               // Join with abstract domain lattice.
               AbstractDomainElement abstrElem1 = determineAbstractElem(state1, value1, lattice, services);
               AbstractDomainElement abstrElem2 = determineAbstractElem(state2, value2, lattice, services);
               
               AbstractDomainElement joinElem = lattice.join(abstrElem1, abstrElem2);
               
               Function skolemConstant =
                     getNewScolemConstantForPrefix(joinElem.toString(), ((Function) value1.op()).sort(), services);
               
               newConstraints.add(joinElem.getDefiningAxiom(tb.func(skolemConstant), services));
               
               joinedVal = tb.func(skolemConstant);
               
            } else {
               
               // No lattice, fall back to if-then-else
               joinedVal = JoinIfThenElse.createIfThenElseTerm(state1, state2, value1, value2, services);
               
            }
            
            return new Pair<Term, LinkedList<Term>>(
                  tb.func((Function) heap1.op(), joinedSubHeap.first, tb.var(pointer1), tb.func(field1), joinedVal),
                  newConstraints);
         }
         
      } else if (((Function) heap1.op()).equals(createFunc) &&
            ((Function) heap2.op()).equals(createFunc)) {
         
         // Create operations.
         
         // Decompose the heap operations.
         Term subHeap1 = heap1.sub(0);
         LocationVariable pointer1 = (LocationVariable) heap1.sub(1).op();
         
         Term subHeap2 = heap2.sub(0);
         LocationVariable pointer2 = (LocationVariable) heap2.sub(1).op();
         
         if (pointer1.equals(pointer2)) {
            // Same objects are created: Join.
            
            Pair<Term, LinkedList<Term>> joinedSubHeap =
                  joinHeaps(subHeap1, subHeap2, state1, state2, services);
            newConstraints.addAll(joinedSubHeap.second);
            
            return new Pair<Term, LinkedList<Term>>(
                  tb.func((Function) heap1.op(), joinedSubHeap.first, tb.var(pointer1)),
                  newConstraints);
         }
         
         // "else" case is fallback at end of method:
         // if-then-else of heaps.
         
      }

      return new Pair<Term, LinkedList<Term>>(
            JoinIfThenElse.createIfThenElseTerm(state1, state2, heap1, heap2, services),
            newConstraints);
   }
}
