package org.key_project.sed.key.ui.command;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.common.ui.testGeneration.ProofGenerateTestsJob;
import org.key_project.sed.key.ui.view.ManualView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;

public class GenerateTestCasesHandlerSED extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      if (AbstractTestGenerator.isSolverAvailable()) {
         if (WorkbenchUtil.findView(ManualView.VIEW_ID) != null) {
            ManualView view = (ManualView) WorkbenchUtil.findView(ManualView.VIEW_ID);
            if (!view.getEnvironment().getProofControl().isInAutoMode()) {
               Proof currentProof = view.getProof();
               IProject currentProject = view.getProject();
               if (currentProof != null && currentProject != null) {
                  Job job = new ProofGenerateTestsJob(currentProject, currentProof, view.getEnvironment().getUi());
                  job.schedule();
               }
            }
         }
      }
      else {
         MessageDialog.openError(HandlerUtil.getActiveShell(event), "Error", "SMT Solver '" + SolverType.Z3_CE_SOLVER + "' is not available.\nPlease configure the SMT Solver Options in the main window of KeY.");
      }
      return null;
   }

}
