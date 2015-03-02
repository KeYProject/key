/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.eclipse;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

/**
 * <p>
 * Provides static methods for logging.
 * </p>
 * <p>
 * The eclipse log can be configured to log also into console or not,
 * see  <a href="http://help.eclipse.org/indigo/index.jsp?topic=%2Forg.eclipse.platform.doc.isv%2Freference%2Fmisc%2Fruntime-options.html">Eclipse runtime option "consoleLog"</a>.
 * </p>
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
   private Plugin plugin;
   
   /**
    * Forbid instances.
    */
   public Logger(Plugin plugin, String plugInId) {
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
   public Plugin getPlugin() {
      return plugin;
   }
   
   /**
    * Logs the warning.
    * @param message The warning message.
    */
   public void logWarning(String message) {
      if (message != null) {
         IStatus status = new Status(IStatus.WARNING, plugInId, message);
         plugin.getLog().log(status);
      }
   }
   
   /**
    * Logs the error.
    * @param message The error message.
    */
   public void logError(String message) {
      if (message != null) {
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
         IStatus status = createErrorStatus(t);
         plugin.getLog().log(status);
      }
   }
   
   /**
    * Logs the error.
    * @param message The error message.
    * @param t The error to log.
    */
   public void logError(String message, Throwable t) {
      if (message != null) {
         IStatus status = new Status(IStatus.ERROR, plugInId, message, t);
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
         if (parentShell == null) {
             parentShell = WorkbenchUtil.getActiveShell();
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