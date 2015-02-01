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

package org.key_project.sed.ui.visualization.action;

import org.eclipse.gef.editparts.ZoomManager;
import org.eclipse.gef.ui.actions.ZoomComboContributionItem;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IPartService;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;

/**
 * Special implementation of {@link ZoomComboContributionItem} which
 * has also a global enabled state defined via {@link IGlobalEnablement}.
 * @author Martin Hentschel
 */
public class GlobalEnablementZoomComboContributionItem extends ZoomComboContributionItem implements IGlobalEnablement {
   /**
    * The global enabled state.
    */
   private boolean globalEnabled;
   
   /**
    * The contributed UI control.
    */
   private Control control;
   
   /**
    * If this {@link ZoomManager} is defined it always used instead of
    * the {@link ZoomManager} which is provided by the active {@link IWorkbenchPart}.
    */
   private ZoomManager fixedZoomManager;
   
   /**
    * Constructor for ComboToolItem.
    * @param partService used to add a PartListener
    * @param initString the initial string displayed in the combo
    */   
   public GlobalEnablementZoomComboContributionItem(IPartService partService, String initString) {
      super(partService, initString);
   }

   /**
    * Constructor for ComboToolItem.
    * @param partService used to add a PartListener
    * @param initStrings the initial string displayed in the combo
    */   
   public GlobalEnablementZoomComboContributionItem(IPartService partService, String[] initStrings) {
      super(partService, initStrings);
   }

   /**
    * Constructor for ComboToolItem.
    * @param partService used to add a PartListener
    */   
   public GlobalEnablementZoomComboContributionItem(IPartService partService) {
      super(partService);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isEnabled() {
      return super.isEnabled() && isGlobalEnabled();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createControl(Composite parent) {
      Control result = super.createControl(parent);
      this.control = result;
      updateEnablement();
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void zoomChanged(double zoom) {
      super.zoomChanged(zoom);
      updateEnablement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setZoomManager(ZoomManager zm) {
      if (fixedZoomManager == null) {
         super.setZoomManager(zm);
      }
      else {
         super.setZoomManager(fixedZoomManager);
      }
      updateEnablement();
   }
   
   /**
    * Updates the enabled state of the contributed UI control ({@link #control}).
    */
   protected void updateEnablement() {
      if (this.control != null && !this.control.isDisposed()) {
         this.control.setEnabled(isEnabled());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGlobalEnabled() {
      return globalEnabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setGlobalEnabled(boolean globalEnabled) {
      this.globalEnabled = globalEnabled;
      updateEnablement();
   }

   /**
    * Returns the fixed {@link ZoomManager} which is always used instead
    * of the provided {@link ZoomManager} by the active {@link IWorkbenchPart}.
    * @return The fixed {@link ZoomManager}.
    */
   public ZoomManager getFixedZoomManager() {
      return fixedZoomManager;
   }

   /**
    * Sets the fixed {@link ZoomManager} which is always used instead
    * of the provided {@link ZoomManager} by the active {@link IWorkbenchPart}.
    * @param fixedZoomManager The fixed {@link ZoomManager} to set.
    */
   public void setFixedZoomManager(ZoomManager fixedZoomManager) {
      this.fixedZoomManager = fixedZoomManager;
      setZoomManager(fixedZoomManager);
   }
}