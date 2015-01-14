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

package de.uka.ilkd.key.rule;

import java.util.HashSet;
import java.util.Iterator;

import de.uka.ilkd.key.abstraction.AbstractDomainElement;
import de.uka.ilkd.key.abstraction.AbstractDomainLattice;
import de.uka.ilkd.key.abstraction.signanalysis.Top;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.util.Pair;

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
   protected Pair<Term, Term> joinStates(
         Pair<Term, Term> state1,
         Pair<Term, Term> state2,
         Term programCounter,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
         
      HashSet<LocationVariable> progVars =
            new HashSet<LocationVariable>();
      
      // Collect program variables in Java block
      progVars.addAll(getProgramLocations(programCounter, services));
      // Collect program variables in update
      progVars.addAll(getUpdateLocations(state1.first));
      
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
         
         if (lattice != null) {
            
            // Join with abstract domain lattice.
            
            AbstractDomainElement abstrElem1 = determineAbstractElem(state1, v, lattice, services);
            AbstractDomainElement abstrElem2 = determineAbstractElem(state2, v, lattice, services);
            
            AbstractDomainElement joinElem = lattice.join(abstrElem1, abstrElem2);
            
            skolemConstant =
                  getNewScolemConstantForPrefix(joinElem.toString(), v.sort(), services);
            
            newConstraints = tb.and(newConstraints, joinElem.getDefiningAxiom(tb.func(skolemConstant), services));
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        tb.func(skolemConstant)));
            
         } else if (!rightSide1.equals(rightSide2)) {
            
            // Apply if-then-else construction: Different values
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        tb.ife(state2.second, rightSide2, rightSide1)));
            
         } else {
            
            // For equal right sides, we just keep those...
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        rightSide1));
            
         }
         
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      // Construct path condition as disjunction
      Term newPathCondition =
            tb.and(
                  createSimplifiedDisjunctivePathCondition(state1.second, state2.second, services),
                  newConstraints);
      
      return new Pair<Term, Term>(newSymbolicState, newPathCondition);
   }
   
   /**
    * Computes and registers a new Skolem constant with the given
    * prefix in its name of the given sort.
    * 
    * @param prefix Prefix for the name of the constant.
    * @param sort Sort of the constant.
    * @param services The services object.
    * @return A new Skolem constant of the given sort with the given
    *     prefix in its name.
    */
   private Function getNewScolemConstantForPrefix(String prefix, Sort sort, Services services) {
      final String newName = services.getTermBuilder().newName(prefix);
      services.getNamespaces().functions().add(new Named() {
         @Override
         public Name name() {
            return new Name(newName);
         }
      });
      
      return new Function(new Name(newName), sort, true);
   }
   
   /**
    * Determines the abstract element suitable for the given variable.
    * This is accomplished by iterating through the abstract elements
    * (from bottom to top) and trying to verify the corresponding axiom
    * instances.
    * 
    * @param state State in which the evaluation of the defining axioms
    *     should be tested.
    * @param variable Variable to find an abstract description for.
    * @param lattice The underlying abstract domain.
    * @param services The services object.
    * @return A suitable abstract element for the given location variable.
    */
   private AbstractDomainElement determineAbstractElem(
         Pair<Term, Term> state,
         LocationVariable variable,
         AbstractDomainLattice<?> lattice,
         Services services) {
      
      TermBuilder tb = services.getTermBuilder();
      
      Iterator<AbstractDomainElement> it = lattice.iterator();
      while (it.hasNext()) {
         AbstractDomainElement elem = it.next();
         
         Term axiom   = elem.getDefiningAxiom(tb.var(variable), services);
         Term appl    = tb.apply(state.first, axiom);
         Term toProve = tb.imp(state.second, appl);
         
         final ProofEnvironment sideProofEnv =
               SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(
                     services.getProof(),                            // Parent Proof
                     false);                                         // useSimplifyTermProfile
         
         try {
            ApplyStrategyInfo proofResult = SideProofUtil.startSideProof(
                  services.getProof(),                                  // Parent proof
                  sideProofEnv,                                         // Proof environment
                  Sequent.createSequent(                                // Sequent to prove
                        Semisequent.EMPTY_SEMISEQUENT,
                        new Semisequent(new SequentFormula(toProve))));
            
            if (proofResult.getProof().closed()) {
               return elem;
            }
         }
         catch (ProofInputException e) {}
      }
      
      return Top.getInstance();
   }
}
