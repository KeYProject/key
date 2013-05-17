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

package org.key_project.sed.key.ui.property;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.launch.AbstractTabbedPropertiesAndLaunchConfigurationTabComposite;
import org.key_project.sed.key.ui.launch.MainLaunchConfigurationComposite;

/**
 * {@link ISection} implementation to show the properties of {@link KeYDebugTarget}s
 * in an {@link MainLaunchConfigurationComposite} instance.
 * @author Martin Hentschel
 */
public class MainKeYDebugTargetPropertySection extends AbstractKeYDebugTargetPropertySection {
   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractTabbedPropertiesAndLaunchConfigurationTabComposite createContentComposite(Composite parent, int style) {
      return new MainLaunchConfigurationComposite(parent, style, null, getWidgetFactory());
   }
}