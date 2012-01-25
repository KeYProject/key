package org.key_project.key4eclipse.starter.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.key4eclipse.util.key.KeYUtil;

/**
 * Handler that starts the KeY UI via {@link KeYUtil#openMainWindow()}.
 */
public class LoadResourceHandler extends AbstractSaveExecutionHandler {
    /**
     * {@inheritDoc}
     */
    @Override
    protected Object doExecute(ExecutionEvent event) throws JavaModelException {
        ISelection selection = HandlerUtil.getCurrentSelection(event);
        if (selection instanceof IStructuredSelection) {
            Object[] elements = ((IStructuredSelection)selection).toArray();
            for (Object element : elements) {
                if (element instanceof IResource) {
                    KeYUtil.load((IResource)element);
                }
                else if (element instanceof IJavaElement) {
                    KeYUtil.load(((IJavaElement)element).getResource());
                }
            }
        }
        return null;
    }
}
