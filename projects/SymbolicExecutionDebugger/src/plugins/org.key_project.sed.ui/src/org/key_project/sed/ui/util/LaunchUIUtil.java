package org.key_project.sed.ui.util;

import java.util.List;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Provides static methods for the UI functionality of the Eclipse Debugger API.
 * @author Martin Hentschel
 */
public final class LaunchUIUtil {
    /**
     * Forbid instances.
     */
    private LaunchUIUtil() {
    }
    
    /**
     * Opens a dialog to select one of the given {@link ILaunchConfiguration}s.
     * @param configurations The available {@link ILaunchConfiguration}s.
     * @param title The dialog title.
     * @return The selected {@link ILaunchConfiguration} or {@code null} if the user cancelled the Dialog.
     */
    public static ILaunchConfiguration chooseConfiguration(List<ILaunchConfiguration> configurations,
                                                           String title) {
        IDebugModelPresentation labelProvider = null;
        try {
            labelProvider = DebugUITools.newDebugModelPresentation();
            ElementListSelectionDialog dialog = new ElementListSelectionDialog(WorkbenchUtil.getActiveShell(), 
                                                                               labelProvider);
            dialog.setElements(configurations.toArray());
            dialog.setTitle(title);  
            dialog.setMessage("&Select existing configuration:");
            dialog.setMultipleSelection(false);
            if (dialog.open() == ElementListSelectionDialog.OK) {
                return (ILaunchConfiguration) dialog.getFirstResult();
            }
            else {
                return null;
            }
        }
        finally {
            if (labelProvider != null) {
                labelProvider.dispose();
            }
        }
    }
}