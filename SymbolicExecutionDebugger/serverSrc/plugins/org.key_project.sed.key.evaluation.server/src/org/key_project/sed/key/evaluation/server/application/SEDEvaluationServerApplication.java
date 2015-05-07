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

package org.key_project.sed.key.evaluation.server.application;

import java.util.Map;

import org.eclipse.equinox.app.IApplication;
import org.eclipse.equinox.app.IApplicationContext;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.PlatformUI;
import org.key_project.sed.key.evaluation.server.implementation.SEDServer;

/**
 * The {@link IApplication} which launches the SED Evaluation Server.
 * @author Martin Hentschel
 */
public class SEDEvaluationServerApplication implements IApplication {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object start(IApplicationContext context) throws Exception {
      SEDServer.main(getStartArguments(context));
      return IApplication.EXIT_OK;
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
}