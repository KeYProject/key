package org.key_project.key4eclipse.starter.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.key_project.key4eclipse.util.key.KeYUtil;

/**
 * Handler that starts the KeY UI via {@link KeYUtil#openMainWindow()}.
 */
public class StartKeYHandler extends AbstractSaveExecutionHandler {
    /**
     * {@inheritDoc}
     */
    @Override
    protected Object doExecute(ExecutionEvent event) throws Exception {
        System.out.println("### START KEY ###");
        KeYUtil.openMainWindow();
        System.out.println("### END KEY ###");
        return null;
    }
}
