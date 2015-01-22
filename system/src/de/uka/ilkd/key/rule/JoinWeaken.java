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
   protected SymbolicExecutionState joinStates(
         SymbolicExecutionState state1,
         SymbolicExecutionState state2,
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
      
      final String varNamePrefix = "v";
      for (LocationVariable v : progVars) {
         final LogicVariable newVar =
               getFreshVariableForPrefix(varNamePrefix, v.sort(), services);
         
         newElementaryUpdates = newElementaryUpdates.prepend(
               tb.elementary(
                     v,
                     tb.var(newVar)));
      }
      
      // Construct weakened symbolic state
      Term newSymbolicState = tb.parallel(newElementaryUpdates);
      
      // Construct path condition as disjunction
      Term newPathCondition =
                  createSimplifiedDisjunctivePathCondition(state1.second, state2.second, services);
      
      return new SymbolicExecutionState(newSymbolicState, newPathCondition);
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
