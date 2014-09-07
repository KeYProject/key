package org.key_project.key4eclipse.resources.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.resources.log.LogManager;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.ui.view.VerificationLogView;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

/**
 * Deletes the log file of the currently selected {@link IProject} in the {@link VerificationLogView}.
 * @author Martin Hentschel
 */
public class ClearLogHandler extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      try {
         IWorkbenchPart part = HandlerUtil.getActivePart(event);
         if (part instanceof VerificationLogView) {
            IProject project = ((VerificationLogView) part).getShownProject();
            if (project != null) {
               IFolder proofFolder = project.getFolder(KeYResourcesUtil.PROOF_FOLDER_NAME);
               if (proofFolder.exists()) {
                  IFile logFile = proofFolder.getFile(LogManager.LOG_FILE_NAME);
                  if (logFile.exists()) {
                     if (MessageDialog.openConfirm(HandlerUtil.getActiveShell(event), "Confirm clear log", "Are you sure you want to clear the log of project \'" + project.getName() + "\'.")) {
                        logFile.delete(true, null);
                     }
                  }
               }
            }
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(HandlerUtil.getActiveShell(event), e);
      }
      return null;
   }
}
