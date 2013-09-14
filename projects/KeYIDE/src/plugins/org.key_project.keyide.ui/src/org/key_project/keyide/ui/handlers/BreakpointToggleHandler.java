package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.Command;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.keyide.ui.breakpoints.KeYBreakpointManager;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionGoalChooser;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionStrategy;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class BreakpointToggleHandler extends AbstractHandler {
   
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      
      
      Command command = event.getCommand();
      boolean oldValue = HandlerUtil.toggleCommandState(command);
      boolean newValue = !oldValue;
      // use the old value and perform the operation
      IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
      if (editorPart != null) {
         final IProofProvider proofProvider = (IProofProvider)editorPart.getAdapter(IProofProvider.class);
         if (proofProvider != null){
            Proof proof = proofProvider.getCurrentProof();
            if(newValue){
               KeYBreakpointManager breakpointManager = (KeYBreakpointManager) editorPart.getAdapter(KeYBreakpointManager.class);
               proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(breakpointManager.getBreakpointStopConditions());
               SymbolicExecutionUtil.updateStrategyPropertiesForSymbolicExecution(proof);
            }else{
               proof.getSettings().getStrategySettings().setCustomApplyStrategyStopCondition(new CompoundStopCondition());
               SymbolicExecutionUtil.updateStrategyPropertiesForSymbolicExecution(proof);
            }
         }
      }
      return null;
   }

}
