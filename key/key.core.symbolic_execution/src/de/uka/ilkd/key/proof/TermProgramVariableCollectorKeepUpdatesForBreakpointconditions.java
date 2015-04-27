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

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.strategy.IBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.AbstractConditionalBreakpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint;

public class TermProgramVariableCollectorKeepUpdatesForBreakpointconditions extends TermProgramVariableCollector {
   private IBreakpointStopCondition breakpointStopCondition;
   
   public TermProgramVariableCollectorKeepUpdatesForBreakpointconditions(Services services, IBreakpointStopCondition breakpointStopCondition) {
       super(services);
       this.breakpointStopCondition = breakpointStopCondition;
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
      for(IBreakpoint breakpoint : breakpointStopCondition.getBreakpoints()){
         if(breakpoint instanceof AbstractConditionalBreakpoint){
            AbstractConditionalBreakpoint conditionalBreakpoint = (AbstractConditionalBreakpoint) breakpoint;
            if(conditionalBreakpoint.getToKeep() != null){
               for(SVSubstitute sub : conditionalBreakpoint.getToKeep()){
                  if(sub instanceof LocationVariable){
                     super.result().add((LocationVariable)sub);
                  }
               }
            }
         }
      }
   }
}