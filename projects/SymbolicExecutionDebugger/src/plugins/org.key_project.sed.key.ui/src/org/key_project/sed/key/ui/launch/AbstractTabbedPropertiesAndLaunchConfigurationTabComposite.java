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

import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.key.core.launch.KeYLaunchSettings;

/**
 * A {@link Composite} which is shown in {@link AbstractTabbedPropertiesAndLaunchConfigurationTab}s.
 * @author Martin Hentschel
 * @see AbstractTabbedPropertiesAndLaunchConfigurationTab
 */
public abstract class AbstractTabbedPropertiesAndLaunchConfigurationTabComposite extends Composite {
   /**
    * An optional {@link MainLaunchConfigurationTab} in which this {@link MainLaunchConfigurationComposite} is shown.
    */
   private AbstractTabbedPropertiesAndLaunchConfigurationTab parentTab;
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    * @param parentTab An optional {@link AbstractTabbedPropertiesAndLaunchConfigurationTab} to make this {@link Composite} editable.
    */
   public AbstractTabbedPropertiesAndLaunchConfigurationTabComposite(Composite parent, int style, AbstractTabbedPropertiesAndLaunchConfigurationTab parentTab) {
      super(parent, style);
      this.parentTab = parentTab;
   }

   /**
    * Checks if this {@link AbstractTabbedPropertiesAndLaunchConfigurationTabComposite} is editable or not.
    * @return {@code true} is editable, {@code false} is read-only.
    */
   protected boolean isEditable() {
      return parentTab != null;
   }
   
   /**
    * Updates the launch configuration dialog.
    */
   protected void updateLaunchConfigurationDialog() {
      if (parentTab != null) {
         parentTab.updateLaunchConfigurationDialog();
      }
   }
   
   /**
    * Returns the parent {@link ILaunchConfigurationDialog} in which this {@link Composite} is shown if available.
    * @return The {@link ILaunchConfigurationDialog} or {@code null} if not available.
    */
   public ILaunchConfigurationDialog getLaunchConfigurationDialog() {
      return parentTab != null ? parentTab.getLaunchConfigurationDialog() : null;
   }
   
   /**
    * Validates the defined settings.
    * @return {@code null} if everything is valid or the error message otherwise.
    */
   public abstract String getNotValidMessage();

   /**
    * Shows the content of the given {@link ILaunchConfiguration}
    * @param configuration The {@link ILaunchConfiguration} to show.
    */
   public abstract void initializeFrom(ILaunchConfiguration configuration);

   public abstract void initializeFrom(KeYLaunchSettings launchSettings);

   /**
    * Stores the defined settings in the given {@link ILaunchConfigurationWorkingCopy}
    * @param configuration The {@link ILaunchConfigurationWorkingCopy} to save to.
    */
   public abstract void performApply(ILaunchConfigurationWorkingCopy configuration);
}