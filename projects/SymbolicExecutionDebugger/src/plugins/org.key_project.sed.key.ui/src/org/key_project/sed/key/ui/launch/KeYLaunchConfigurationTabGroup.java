package org.key_project.sed.key.ui.launch;

import org.eclipse.debug.ui.AbstractLaunchConfigurationTabGroup;
import org.eclipse.debug.ui.CommonTab;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.debug.ui.ILaunchConfigurationTab;
import org.eclipse.debug.ui.sourcelookup.SourceLookupTab;

/**
 * {@link AbstractLaunchConfigurationTabGroup} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYLaunchConfigurationTabGroup extends AbstractLaunchConfigurationTabGroup {
    /**
     * {@inheritDoc}
     */
    @Override
    public void createTabs(ILaunchConfigurationDialog dialog, String mode) {
        setTabs(new ILaunchConfigurationTab[] {new MainLaunchConfigurationTab(), // KeY specific tab 
                                               new KeYCustomizationLaunchConfigurationTab(), // KeY specific customization tab
                                               new SourceLookupTab(),  // General source lookup tab
                                               new CommonTab()}); // General common tab.
    }
}
