// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.symbolic_execution.strategy.ConditionalBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;

public class TermProgramVariableCollectorKeepUpdatesForBreakpointconditions extends TermProgramVariableCollector {
   private CompoundStopCondition parentCondition;
   
   public TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(Services services, CompoundStopCondition parentCondition) {
       super(services);
       this.parentCondition=parentCondition;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void visit(Term t) {
      super.visit(t);
      if (t.op() instanceof Modality) {
         addVarsToKeep();
      }
   }
   
   private void addVarsToKeep() {
      for(IStopCondition stopCondition : parentCondition.getChildren()){
         if(stopCondition instanceof ConditionalBreakpointStopCondition){
            ConditionalBreakpointStopCondition lineBreakpoint = (ConditionalBreakpointStopCondition) stopCondition;
            if(lineBreakpoint.getToKeep()!=null){
               for(SVSubstitute sub : lineBreakpoint.getToKeep()){
                  if(sub instanceof LocationVariable){
                     super.result().add((LocationVariable)sub);
                  }
               }
            }
         }
      }
   }

}
