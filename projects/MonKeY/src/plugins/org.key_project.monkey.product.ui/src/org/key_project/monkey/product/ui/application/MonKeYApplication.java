/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.monkey.product.ui.application;

import java.util.Comparator;
import java.util.Map;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
import org.key_project.monkey.product.ui.batch.MonKeYBatchMode;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.SwingUtil;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;

/**
 * <p>
 * Special implementation of {@link IApplication} for the product "MonKeY".
 * </p>
 * <p>
 * For more information about RCP based products have a look at:
 * <a href="http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application">http://javawiki.sowas.com/doku.php?id=eclipse-rcp:source-example-application</a>
 * </p> 
 * @author Martin Hentschel
 */
public class MonKeYApplication implements IApplication {
   /**
    * Parameter to show KeY's {@link MainWindow} instead of MonKeY.
    */
   public static final String PARAM_KEY_ONLY = "-keyonly";
   
   /**
    * Parameter to use the batch mode.
    */
   public static final String PARAM_BATCH_MODE = "-batch";
  
   /**
    * {@inheritDoc}
    */
   @Override
   public Object start(IApplicationContext context) throws Exception {
      String[] arguments = getStartArguments(context);
      Comparator<String> comparator = StringUtil.createIgnoreCaseComparator();
      if (ArrayUtil.contains(arguments, PARAM_KEY_ONLY, comparator)) {
         String[] cleaned = ArrayUtil.remove(arguments, PARAM_KEY_ONLY, comparator);
         return startKeYApplication(cleaned, context);
      }
      else if (ArrayUtil.contains(arguments, PARAM_BATCH_MODE, comparator)) {
         String[] cleaned = ArrayUtil.remove(arguments, PARAM_BATCH_MODE, comparator);
         return startBatchApplication(cleaned, context);
      }
      else {
         return startEclipseApplication(context);
      }
   }
    
   /**
    * Starts the batch mode.
    * @param cleanedArguments The cleaned arguments for the batch mode.
    * @param context The {@link IApplicationContext} to use.
     * @return The exit result.
     * @throws Exception Occurred Exception.
    */
   protected Object startBatchApplication(String[] cleanedArguments, IApplicationContext context) throws Exception {
      try {
         // Close splash screen
         context.applicationRunning();
         new MonKeYBatchMode().start(cleanedArguments);
         return IApplication.EXIT_OK;
      }
      catch (Exception e) {
         e.printStackTrace(); // Throwing the exception opens an UI dialog which should not happen in batch execution.
         return IApplication.EXIT_OK;
      }
   }

   /**
     * Starts the KeY application.
     * @param cleanedArguments The cleaned arguments for KeY.
     * @param context The {@link IApplicationContext} to use.
     * @return The exit result.
     * @throws Exception Occurred Exception.
     */
    protected Object startKeYApplication(final String[] cleanedArguments,
                                         final IApplicationContext context) throws Exception {
        // Start KeY
        SwingUtil.invokeAndWait(new Runnable() {
            @Override
            public void run() {
                Main.main(cleanedArguments);
            }
        });
        // Close splash screen
        context.applicationRunning();
        // Wait until KeY is closed.
        MainWindow mainWindow = MainWindow.getInstance();
        while (mainWindow.isVisible()) {
            Thread.sleep(500);
        }
        return IApplication.EXIT_OK;
    }

    /**
     * Starts the eclipse application.
     * @param context The {@link IApplicationContext} to use.
     * @return The exit result.
     * @throws Exception Occurred Exception.
     */
    protected Object startEclipseApplication(IApplicationContext context) throws Exception {
        Display display = PlatformUI.createDisplay();
        try {
            int returnCode = PlatformUI.createAndRunWorkbench(display, new MonKeYWorkbenchAdvisor());
            if (returnCode == PlatformUI.RETURN_RESTART) {
                return IApplication.EXIT_RESTART;
            }
            return IApplication.EXIT_OK;
        }
        finally {
            display.dispose();
        }
    }
    
    /**
     * Returns the start parameters if possible.
     * @param context The {@link IApplicationContext} to use.
     * @return The found start parameters or {@code null} if no one was found.
     */
    protected String[] getStartArguments(IApplicationContext context) {
        if (context != null) {
            Map<?, ?> arguments = context.getArguments();
            if (arguments != null) {
                Object value = arguments.get(IApplicationContext.APPLICATION_ARGS);
                return value instanceof String[] ? (String[])value : null;
            }
            else {
                return null;
            }
        }
        else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void stop() {
        final IWorkbench workbench = PlatformUI.getWorkbench();
        if (workbench == null) {
            return;
        }
        final Display display = workbench.getDisplay();
        display.syncExec(new Runnable() {
            public void run() {
                if (!display.isDisposed()) {
                    workbench.close();
                }
            }
        });
    }
}