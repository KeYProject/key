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

package org.key_project.sed.example.ui.launch;

import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTabGroup;
import org.eclipse.debug.ui.CommonTab;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.debug.ui.ILaunchConfigurationTab;
import org.eclipse.debug.ui.sourcelookup.SourceLookupTab;

/**
 * An {@link AbstractLaunchConfigurationTabGroup} creates the tabs shown in the 
 * edit dialog of {@link ILaunchConfiguration}s.
 * <p>
 * For the example symbolic execution engine only the general tabs 
 * {@link SourceLookupTab} and {@link CommonTab} are available.
 * @author Martin Hentschel
 */
public class ExampleLaunchConfigurationTabGroup extends AbstractLaunchConfigurationTabGroup {
    /**
     * {@inheritDoc}
     */
    @Override
    public void createTabs(ILaunchConfigurationDialog dialog, String mode) {
        setTabs(new ILaunchConfigurationTab[] {// Return your own tabs to edit the symbolic execution engine specific properties of an ILaunchConfiguration.
                                               new SourceLookupTab(),  // General source lookup tab
                                               new CommonTab()}); // General common tab.
    }
}