package org.key_project.key4eclipse.starter.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.dialogs.ErrorDialog;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.starter.ui.Activator;

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
        IStatus status = new Status(IStatus.ERROR, Activator.PLUGIN_ID, t.getMessage(), t);
        return ErrorDialog.openError(HandlerUtil.getActiveShell(event),
                                     "Error", 
                                     null,
                                     status);
    }
}
