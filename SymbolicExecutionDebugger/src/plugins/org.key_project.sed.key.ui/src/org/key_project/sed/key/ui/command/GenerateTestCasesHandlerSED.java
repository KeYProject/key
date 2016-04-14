package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.keyide.ui.handlers.GenerateTestCasesHandler;
import org.key_project.sed.key.ui.view.ProofView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;

/**
 * Class to handle the generate test cases command on {@link ProofView}.
 * @author Seena Vellaramkalayil
 *
 */
public class GenerateTestCasesHandlerSED extends AbstractSaveExecutionHandler {

   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      if (AbstractTestGenerator.isSolverAvailable()) {
         if (WorkbenchUtil.findView(ProofView.VIEW_ID) != null) {
            ProofView view = (ProofView) WorkbenchUtil.findView(ProofView.VIEW_ID);
            if (!view.getEnvironment().getProofControl().isInAutoMode()) {
               GenerateTestCasesHandler.generateTestCases(view.getCurrentProof(), view.getProject(), view.getUI());
            }
         }
      } 
      else {
         MessageDialog.openError(HandlerUtil.getActiveShell(event), "Error", "SMT Solver '" + SolverType.Z3_CE_SOLVER + "' is not available.\nPlease configure the SMT Solver Options in the main window of KeY.");
      }
      return null;
   }
}
