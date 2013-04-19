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
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.AbstractPropertySection;

/**
 * Provides a basic functionality for {@link AbstractLaunchConfigurationTab}s
 * which are also shown in an {@link AbstractPropertySection}.
 * @author Martin Hentschel
 */
public abstract class AbstractTabbedPropertiesAndLaunchConfigurationTab extends AbstractLaunchConfigurationTab {
   /**
    * Contains the shown content.
    */
   private AbstractTabbedPropertiesAndLaunchConfigurationTabComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Root
      Composite rootComposite = new Composite(parent, SWT.NONE);
      setControl(rootComposite);
      rootComposite.setLayout(new FillLayout());
      // Content
      contentComposite = createContentComposite(rootComposite, SWT.NONE);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (contentComposite != null) {
         contentComposite.dispose();
      }
      super.dispose();
   }

   /**
    * Creates the shown {@link AbstractTabbedPropertiesAndLaunchConfigurationTabComposite}.
    * @param parent The parent {@link Composite}.
    * @param style The style.
    * @return The created {@link AbstractTabbedPropertiesAndLaunchConfigurationTabComposite}.
    */
   protected abstract AbstractTabbedPropertiesAndLaunchConfigurationTabComposite createContentComposite(Composite parent, int style);

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isValid(ILaunchConfiguration launchConfig) {
      boolean valid = super.isValid(launchConfig);
      if (valid) {
         String message = contentComposite.getNotValidMessage();
         if (message != null) {
            valid = false;
            setErrorMessage(message);
         }
      }
      if (valid) {
         setErrorMessage(null);
      }
      return valid;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setDefaults(ILaunchConfigurationWorkingCopy configuration) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeFrom(ILaunchConfiguration configuration) {
      contentComposite.initializeFrom(configuration);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void performApply(ILaunchConfigurationWorkingCopy configuration) {
      contentComposite.performApply(configuration);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public ILaunchConfigurationDialog getLaunchConfigurationDialog() {
      return super.getLaunchConfigurationDialog();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void updateLaunchConfigurationDialog() {
      super.updateLaunchConfigurationDialog();
   }
}