package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.common.ui.testGeneration.ProofGenerateTestsJob;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.testgen.AbstractTestGenerator;

/**
 * Handler to generate test cases.
 * @author Martin Hentschel
 */
public class GenerateTestCasesHandler extends AbstractSaveExecutionHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      if (AbstractTestGenerator.isSolverAvailable()) {
         IWorkbenchPart workbenchPart = HandlerUtil.getActivePart(event);
         if (!(workbenchPart instanceof IProofProvider)) {
            workbenchPart = HandlerUtil.getActiveEditor(event);
         }
         if (workbenchPart instanceof IProofProvider) {
            IProofProvider provider = (IProofProvider) workbenchPart;
            if (!provider.getProofControl().isInAutoMode()) {
               generateTestCases(provider.getCurrentProof(), provider.getProject(), provider.getUI());
            }
         }
      }
      else {
         MessageDialog.openError(HandlerUtil.getActiveShell(event), "Error", "SMT Solver '" + SolverType.Z3_CE_SOLVER + "' is not available.\nPlease configure the SMT Solver Options in the main window of KeY.");
      }
      return null;
   }
   
   /**
    * Generate test cases.
    * @param currentProof The current {@link Proof}.
    * @param currentProject The current {@link IProject}.
    * @param ui The {@link UserInterfaceControl} to use.
    */
   public static void generateTestCases(Proof currentProof, IProject currentProject, UserInterfaceControl ui) {
      if (currentProof != null && currentProject != null) {
         Job job = new ProofGenerateTestsJob(currentProject, currentProof, ui);
         job.schedule();
      }
   }
}
