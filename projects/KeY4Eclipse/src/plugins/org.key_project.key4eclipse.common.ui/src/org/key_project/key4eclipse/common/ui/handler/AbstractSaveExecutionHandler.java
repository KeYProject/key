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

package org.key_project.key4eclipse.common.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.common.ui.util.LogUtil;

/**
 * Provides a basic implementation of {@link AbstractHandler} that allows
 * to execute code that might throw an {@link Exception}. 
 * Caught {@link Exception} are shown to the user and logged in the 
 * Eclipse log via the default command API.
 * @author Martin Hentschel
 */
public abstract class AbstractSaveExecutionHandler extends AbstractHandler {
    /**
     * {@inheritDoc}
     */
    @Override
    public Object execute(ExecutionEvent event) throws ExecutionException {
        try {
            return doExecute(event);
        }
        catch (Exception e) {
            openErrorDialog(event, e);
            throw new ExecutionException(e.getMessage(), e);
        }
    }
    
    /**
     * Executes the code that might throws an {@link Exception}.
     * @param event The {@link ExecutionEvent} to handle.
     * @return The result.
     * @throws Exception Occurred Exception.
     */
    protected abstract Object doExecute(ExecutionEvent event) throws Exception;
    
    /**
     * Opens an {@link ErrorDialog} that shows the given {@link Throwable}.
     * @param event The handled {@link ExecutionEvent}.
     * @param t The {@link Throwable} to show in an {@link ErrorDialog}.
     * @return The dialog result of the shown {@link ErrorDialog} instance.
     */
    protected int openErrorDialog(ExecutionEvent event, Throwable t) {
        return LogUtil.getLogger().openErrorDialog(HandlerUtil.getActiveShell(event), t);
    }
}