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

package org.key_project.sed.key.ui.launch;

import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.key.ui.util.KeYSEDImages;

/**
 * {@link AbstractLaunchConfigurationTab} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class MainLaunchConfigurationTab extends AbstractTabbedPropertiesAndLaunchConfigurationTab {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Main";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return KeYSEDImages.getImage(KeYSEDImages.LAUNCH_MAIN_TAB_GROUP);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected AbstractTabbedPropertiesAndLaunchConfigurationTabComposite createContentComposite(Composite parent, int style) {
      return new MainLaunchConfigurationComposite(parent, style, this, null);
   }
}