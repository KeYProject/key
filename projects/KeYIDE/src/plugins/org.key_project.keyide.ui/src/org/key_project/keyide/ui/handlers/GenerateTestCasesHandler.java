package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.handler.AbstractSaveExecutionHandler;
import org.key_project.key4eclipse.common.ui.testGeneration.ProofGenerateTestsJob;
import org.key_project.keyide.ui.editor.KeYEditor;

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
         IEditorPart editorPart = HandlerUtil.getActiveEditor(event);
         if (editorPart instanceof KeYEditor) {
            KeYEditor editor = (KeYEditor) editorPart;
            if (!editor.getMediator().isInAutoMode()) {
               Proof currentProof = editor.getCurrentProof();
               IProject currentProject = editor.getProject();
               if (currentProof != null && currentProject != null) {
                  Job job = new ProofGenerateTestsJob(currentProject, currentProof, editor.getMediator());
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
