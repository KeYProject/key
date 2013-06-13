package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.gui.ApplyStrategy.IStopCondition;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.LineBreakpointStopCondition;

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
         if(stopCondition instanceof LineBreakpointStopCondition){
            LineBreakpointStopCondition lineBreakpoint = (LineBreakpointStopCondition) stopCondition;
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
