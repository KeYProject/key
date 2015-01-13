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
import de.uka.ilkd.key.abstraction.signanalysis.SignAnalysisLattice;
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
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SideProofUtil;
import de.uka.ilkd.key.util.Pair;

//TODO: In JoinRule: Must probably add some universal closure for the
//      new logical variables...

/**
 * Rule that joins two sequents based on a sign lattice
 * for integers. No-Integer-Variables (booleans, heap)
 * are just set to fresh variables.
 * 
 * @author Dominic Scheurer
 */
public class JoinWithSignLattice extends JoinRule {
   
   public static final JoinWithSignLattice INSTANCE = new JoinWithSignLattice();
   private static final String DISPLAY_NAME = "JoinBySignLatticeAbstraction";
   private static final Name RULE_NAME = new Name(DISPLAY_NAME);

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
      
      final Sort intSort =
            (Sort) services.getNamespaces().sorts().lookup(new Name("int"));
      final String varNamePrefix = "v";
      
      for (LocationVariable v : progVars) {

         final String newName = tb.newName(varNamePrefix);
         services.getNamespaces().variables().add(new Named() {
            @Override
            public Name name() {
               return new Name(newName);
            }
         });
         
         LogicVariable freshVariable = new LogicVariable(new Name(newName), v.sort());
         
         newElementaryUpdates = newElementaryUpdates.prepend(
               tb.elementary(
                     v,
                     tb.var(freshVariable)));
         
         if (v.sort().equals(intSort)) {
            
            Term rightSide1 = getUpdateRightSideFor(state1.first, v);
            Term rightSide2 = getUpdateRightSideFor(state2.first, v);
            
            if (rightSide1 == null) {
               rightSide1 = tb.var(v);
            }
            
            if (rightSide2 == null) {
               rightSide2 = tb.var(v);
            }
            
            AbstractDomainLattice<AbstractDomainElement, Integer> lattice =
                  SignAnalysisLattice.getInstance();
            
            AbstractDomainElement abstrElem1 = determineAbstractElem(state1, v, lattice, services);
            AbstractDomainElement abstrElem2 = determineAbstractElem(state2, v, lattice, services);
            
            AbstractDomainElement joinElem = lattice.join(abstrElem1, abstrElem2);
            
            newConstraints = tb.and(newConstraints, joinElem.getDefiningAxiom(freshVariable, services));
            
         }
         
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      // Construct path condition as disjunction
      Term newPathCondition = tb.and(tb.or(state1.second, state2.second), newConstraints);
      
      return new Pair<Term, Term>(newSymbolicState, newPathCondition);
   }
   
   private AbstractDomainElement determineAbstractElem(
         Pair<Term, Term> state,
         LocationVariable variable,
         AbstractDomainLattice<AbstractDomainElement, Integer> lattice,
         Services services) {
      
      TermBuilder tb = services.getTermBuilder();
      
      Iterator<AbstractDomainElement> it = lattice.iterator();
      while (it.hasNext()) {
         AbstractDomainElement elem = it.next();
         
         Term axiom   = elem.getDefiningAxiom(variable, services);
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

   @Override
   public Name name() {
      return RULE_NAME;
   }

   @Override
   public String displayName() {
      return DISPLAY_NAME;
   }
   
   @Override
   public String toString() {
      return DISPLAY_NAME;
   }
}
