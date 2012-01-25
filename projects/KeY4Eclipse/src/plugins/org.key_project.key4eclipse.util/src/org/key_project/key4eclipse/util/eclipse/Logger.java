/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package org.key_project.key4eclipse.util.eclipse;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithResult;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithResult;

/**
 * Provides static methods for logging.
 * @author Martin Hentschel
 */
public class Logger {
   /**
    * The plug-in id to use in logs.
    */
   private String plugInId;
   
   /**
    * The plug-in that provides the eclipse logger.
    */
   private AbstractUIPlugin plugin;
   
   /**
    * Forbid instances.
    */
   public Logger(AbstractUIPlugin plugin, String plugInId) {
      this.plugInId = plugInId;
      this.plugin = plugin;
   }

   /**
    * Returns the plug-in id to use in logs.
    * @return The plug-in id to use in logs.
    */
   public String getPlugInId() {
      return plugInId;
   }

   /**
    * Returns the plug-in that provides the eclipse logger.
    * @return The plug-in that provides the eclipse logger.
    */
   public AbstractUIPlugin getPlugin() {
      return plugin;
   }
   
   /**
    * Logs the warning.
    * @param message The warning.
    */
   public void logWarning(String message) {
      if (message != null) {
         System.out.println(message);
         IStatus status = new Status(IStatus.WARNING, plugInId, message);
         plugin.getLog().log(status);
      }
   }
   
   /**
    * Logs the error.
    * @param message The warning.
    */
   public void logError(String message) {
      if (message != null) {
         System.out.println(message);
         IStatus status = new Status(IStatus.ERROR, plugInId, message);
         plugin.getLog().log(status);
      }
   }
   
   /**
    * Logs the error.
    * @param t The error to log.
    */
   public void logError(Throwable t) {
      if (t != null) {
         t.printStackTrace();
         IStatus status = createErrorStatus(t);
         plugin.getLog().log(status);
      }
   }
   
   /**
    * Creates an error status.
    * @param t The exception.
    * @return The created error status.
    */
   public IStatus createErrorStatus(Throwable t) {
      return new Status(IStatus.ERROR, plugInId, t.getMessage(), t);
   }
   
   /**
    * Creates an error status.
    * @param message The error message.
    * @return The created error status.
    */
   public IStatus createErrorStatus(String message) {
      return new Status(IStatus.ERROR, plugInId, message);
   }

   /**
    * Creates an error status.
    * @param message The error message.
    * @param t The exception.
    * @return The created error status.
    */
   public IStatus createErrorStatus(String message, Throwable t) {
      return new Status(IStatus.ERROR, plugInId, message, t);
   }
   
   /**
    * Opens an error dialog thread save.
    * @param parentShell The parent {@link Shell}.
    * @param t The exception to show.
    * @return The dialog result or {@code -1} if no dialog was opened or {@code -2} if no dialog result was received.
    */
   public int openErrorDialog(Shell parentShell,
                              final Throwable t) {
      if (t != null) {
         if (parentShell == null && PlatformUI.getWorkbench() != null) {
            IWorkbenchWindow window = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
            if (window != null) {
               parentShell = window.getShell();
            }
         }
         final Shell parentToUse = parentShell;
         IRunnableWithResult<Integer> run = new AbstractRunnableWithResult<Integer>() {
            @Override
            public void run() {
               setResult(ErrorDialog.openError(parentToUse, "Error", null, createErrorStatus(t)));
            }
         };
         if (parentShell != null) {
            parentShell.getDisplay().syncExec(run);
         }
         else {
            Display.getDefault().syncExec(run);
         }
         return run.getResult() != null ? run.getResult() : -2;
      }
      else {
         return -1;
      }
   }
}
