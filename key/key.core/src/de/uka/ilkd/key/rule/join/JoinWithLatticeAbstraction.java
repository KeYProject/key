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

import de.uka.ilkd.key.axiom_abstraction.AbstractDomainElement;
import de.uka.ilkd.key.axiom_abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.axiom_abstraction.signanalysis.Top;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.joinrule.SymbolicExecutionState;
import static de.uka.ilkd.key.util.joinrule.JoinRuleUtils.*;

/**
 * Rule that joins two sequents based on a specified set of
 * abstract domain lattices. If no lattice is specified for
 * a given sort, the rule proceeds such that program variables
 * are unchanged if they are equal in both states and applies
 * the if-then-else construction otherwise.
 * 
 * @author Dominic Scheurer
 */
public abstract class JoinWithLatticeAbstraction implements JoinProcedure {

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
   public Pair<HashSet<Term>, Term> joinValuesInStates(
         LocationVariable v,
         SymbolicExecutionState state1,
         Term valueInState1,
         SymbolicExecutionState state2,
         Term valueInState2,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
      
      HashSet<Term> newConstraints = new HashSet<Term>();
      
      AbstractDomainLattice<?> lattice = getAbstractDomainForSort(valueInState1.sort(), services);
      
      if (lattice != null) {
         
         // Join with abstract domain lattice.
         AbstractDomainElement abstrElem1 = determineAbstractElem(state1, valueInState1, lattice, services);
         AbstractDomainElement abstrElem2 = determineAbstractElem(state2, valueInState2, lattice, services);
         
         AbstractDomainElement joinElem = lattice.join(abstrElem1, abstrElem2);
         
         Function skolemConstant =
               getNewSkolemConstantForPrefix(joinElem.toString(), valueInState1.sort(), services);
         
         newConstraints.add(joinElem.getDefiningAxiom(tb.func(skolemConstant), services));
         //NOTE: We also remember the precise values by if-then-else construction. This
         //      preserves completeness and should also not be harmful to performance in
         //      cases where completeness is also preserved by the lattice. However, if
         //      there are lattices where this construction is bad, it may be safely
         //      removed (no harm to soundness!).
         newConstraints.add(tb.equals(tb.func(skolemConstant),
               JoinIfThenElse.createIfThenElseTerm(state1, state2, valueInState1, valueInState2, services)));
         
         return new Pair<HashSet<Term>, Term>(newConstraints, tb.func(skolemConstant));
         
      } else {
         
         return new Pair<HashSet<Term>, Term>(
               new HashSet<Term>(),
               JoinIfThenElse.createIfThenElseTerm(state1, state2, valueInState1, valueInState2, services));
         
      }
      
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
   
}
