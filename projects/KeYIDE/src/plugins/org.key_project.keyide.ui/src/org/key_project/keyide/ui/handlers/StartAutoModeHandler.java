package org.key_project.keyide.ui.handlers;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandlerListener;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.key_project.keyide.ui.util.KeYToUIUtil;
import org.key_project.keyide.ui.views.Outline;

import de.uka.ilkd.key.gui.prooftree.GUIProofTreeModel;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;
import de.uka.ilkd.key.ui.UserInterface;

public class StartAutoModeHandler extends AbstractSaveExecutionHandler {

   @Override
   protected Object doExecute(ExecutionEvent event) throws Exception {
      new Job("Auto Mode"){
      @Override
      protected IStatus run(IProgressMonitor monitor) {
         CustomConsoleUserInterface ui = (CustomConsoleUserInterface) KeYToUIUtil.getUi();
         Proof proof = KeYToUIUtil.getProof();
         //step by step
         ui.getMediator().setMaxAutomaticSteps(1);
         
         ui.startAndWaitForProof(proof);
         
         monitor.beginTask("Auto Mode", 0);
         return Status.OK_STATUS;
      }
      }.schedule();
      return null;
   }

}
