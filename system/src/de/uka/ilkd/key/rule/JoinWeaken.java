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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.util.Pair;

/**
 * Rule that joins two sequents based on "total" weakening:
 * Replacement of symbolic state by an update setting every
 * program variable to a fresh logical variable.
 * 
 * @author Dominic Scheurer
 */
public class JoinWeaken extends JoinRule {
   
   public static final JoinWeaken INSTANCE = new JoinWeaken();
   private static final String DISPLAY_NAME = "JoinByWeakening";
   private static final Name RULE_NAME = new Name(DISPLAY_NAME);

   @Override
   protected Pair<Term, Term> joinStates(
         ImmutableList<Pair<Term, Term>> states,
         Term programCounter,
         Services services) {
      
      final TermBuilder tb = services.getTermBuilder();
      
      Pair<Term, Term> joinedState = states.head();
      states = states.tail();
      
      for (Pair<Term,Term> state : states) {
         
         HashSet<LocationVariable> progVars =
               new HashSet<LocationVariable>();
         
         // Collect program variables in Java block
         progVars.addAll(getProgramLocations(programCounter, services));
         // Collect program variables in update
         progVars.addAll(getUpdateLocations(joinedState.first));
         
         ImmutableList<Term> newElementaryUpdates = ImmutableSLList.nil();
         
         int varNameCounter = (int) System.currentTimeMillis();
         final String varNamePrefix = "v_";
         for (LocationVariable v : progVars) {
            String newName = varNamePrefix + (varNameCounter++);
            
            newElementaryUpdates = newElementaryUpdates.prepend(
                  tb.elementary(
                        v,
                        tb.var(
                              new LogicVariable(new Name(newName), v.sort()))));
         }
         
         // Construct weakened symbolic state
         Term newSymbolicState = tb.parallel(newElementaryUpdates);
         
         // Construct path condition as disjunction
         Term newPathCondition = tb.or(joinedState.second, state.second);
         
         joinedState = new Pair<Term, Term>(newSymbolicState, newPathCondition);
      }
      
      return joinedState;
   }

   @Override
   public Name name() {
      return RULE_NAME;
   }

   @Override
   public String displayName() {
      return DISPLAY_NAME;
   }
}
