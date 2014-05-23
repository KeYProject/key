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

package org.key_project.sed.key.ui.property;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.ISection;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetPage;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.sed.key.ui.launch.AbstractTabbedPropertiesAndLaunchConfigurationTabComposite;
import org.key_project.sed.ui.property.AbstractSEDDebugTargetPropertySection;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * Provides a basic {@link ISection} implementation to show the properties of {@link KeYDebugTarget}s
 * via {@link AbstractTabbedPropertiesAndLaunchConfigurationTabComposite} instances.
 * @author Martin Hentschel
 */
public abstract class AbstractKeYDebugTargetPropertySection extends AbstractSEDDebugTargetPropertySection {
   /**
    * The shown content.
    */
   private AbstractTabbedPropertiesAndLaunchConfigurationTabComposite contentComposite;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControls(Composite parent, TabbedPropertySheetPage tabbedPropertySheetPage) {
      super.createControls(parent, tabbedPropertySheetPage);
      contentComposite = createContentComposite(parent, SWT.NONE);
   }
   
   /**
    * Creates the {@link AbstractTabbedPropertiesAndLaunchConfigurationTabComposite} to use.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    * @return The created {@link AbstractTabbedPropertiesAndLaunchConfigurationTabComposite}.
    */
   protected abstract AbstractTabbedPropertiesAndLaunchConfigurationTabComposite createContentComposite(Composite parent, int style);

   /**
    * {@inheritDoc}
    */
   @Override
   public void refresh() {
      KeYDebugTarget target = getDebugTarget();
      contentComposite.initializeFrom(target != null ? target.getLaunchSettings() : null);
   }
   
   /**
    * Returns the {@link KeYDebugTarget} to show.
    * @return The {@link KeYDebugTarget} to show or {@code null} if no one should be shown.
    */
   protected KeYDebugTarget getDebugTarget() {
      Object object = SWTUtil.getFirstElement(getSelection());
      return getKeYDebugTarget(object);
   }
   
   /**
    * Converts the given {@link Object} into a {@link KeYDebugTarget} if possible.
    * @param object The given {@link Object}.
    * @return The {@link KeYDebugTarget} or {@code null} if conversion is not possible.
    */
   public static KeYDebugTarget getKeYDebugTarget(Object object) {
      ISEDDebugTarget target = AbstractKeYDebugTargetPropertySection.getDebugTarget(object);
      return target instanceof KeYDebugTarget ? (KeYDebugTarget)target : null;
   }
}