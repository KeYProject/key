package org.key_project.sed.key.ui.launch;

import org.eclipse.debug.ui.ILaunchShortcut;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorPart;

/**
 * {@link ILaunchShortcut} implementation for Symbolic Executiong Debugger
 * based on KeY.
 * @author Martin Hentschel
 */
public class KeYLaunchShortcut implements ILaunchShortcut {
    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(ISelection selection, String mode) {
        System.out.println("launch shortcut: " + selection);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(IEditorPart editor, String mode) {
        System.out.println("launch shortcut: " + editor);
    }
}
