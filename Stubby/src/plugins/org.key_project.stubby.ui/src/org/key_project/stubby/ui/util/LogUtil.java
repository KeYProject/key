package org.key_project.stubby.ui.util;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.stubby.ui.Activator;

/**
 * Provides static methods for logging.
 * @author Martin Hentschel
 */
public final class LogUtil {
   /**
    * Logs the error.
    * @param t The error to log.
    */
   public static void logError(Throwable t) {
      if (t != null) {
         IStatus status = createErrorStatus(t);
         Activator.getDefault().getLog().log(status);
      }
   }
   
   /**
    * Creates an error status.
    * @param t The exception.
    * @return The created error status.
    */
   public static IStatus createErrorStatus(Throwable t) {
      return new Status(IStatus.ERROR, Activator.PLUGIN_ID, t.getMessage(), t);
   }

   /**
    * Opens an error dialog.
    * @param t The exception to show in an error dialog.
    * @param parentShell The parent {@link Shell} to use.
    */
   public static void openErrorDialog(final Throwable t, final Shell parentShell) {
      parentShell.getDisplay().syncExec(new Runnable() {
         @Override
         public void run() {
            ErrorDialog.openError(parentShell, "Error", null, createErrorStatus(t));
         }
      });
   }
}