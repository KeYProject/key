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

package org.key_project.key4eclipse.common.ui.wizard;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.common.ui.util.StarterDescription;
import org.key_project.key4eclipse.common.ui.util.StarterPreferenceUtil;
import org.key_project.key4eclipse.common.ui.util.StarterUtil;
import org.key_project.key4eclipse.common.ui.wizard.page.StarterWizardPage;

import de.uka.ilkd.key.collection.ImmutableList;

/**
 * {@link StarterWizard} to select a {@link StarterDescription}.
 * @author Martin Hentschel
 */
public class StarterWizard<I> extends Wizard {
   /**
    * The selected {@link StarterDescription}.
    */
   private StarterDescription<I> selectedStarter;
   
   /**
    * The available {@link StarterDescription}s.
    */
   private ImmutableList<StarterDescription<I>> starterDescriptions;

   /**
    * The property to store the selected {@link StarterDescription} in {@link StarterPreferenceUtil#getStore()}.
    */
   private String selectedStarterProperty;
   
   /**
    * The property with the do not ask again option in {@link StarterPreferenceUtil#getStore()}.
    */
   private String dontAskAgainProperty;
   
   /**
    * The property with the disabled option in {@link StarterPreferenceUtil#getStore()}.
    */
   private String disableProperty;
   
   /**
    * The used {@link StarterWizardPage}.
    */
   private StarterWizardPage<I> starterPage;
   
   /**
    * Listens for changes on {@link StarterPreferenceUtil#getStore()}.
    */
   private IPropertyChangeListener propertyListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         updateValues();
      }
   };
   
   /**
    * Constructor.
    * @param wizardTitle The wizard title.
    * @param starterPageTitle The starter page title.
    * @param starterPageDescription The starter page description.
    * @param starterDescriptions The available {@link StarterDescription}s.
    * @param selectedStarterProperty The property to store the selected {@link StarterDescription} in {@link StarterPreferenceUtil#getStore()}.
    * @param dontAskAgainProperty The property with the do not ask again option in {@link StarterPreferenceUtil#getStore()}.
    * @param disableProperty The property with the disabled option in {@link StarterPreferenceUtil#getStore()}.
    */
   public StarterWizard(String wizardTitle,
                        String starterPageTitle,
                        String starterPageDescription,
                        ImmutableList<StarterDescription<I>> starterDescriptions,
                        String selectedStarterProperty,
                        String dontAskAgainProperty,
                        String disableProperty) {
      Assert.isNotNull(starterDescriptions);
      Assert.isNotNull(selectedStarterProperty);
      Assert.isNotNull(dontAskAgainProperty);
      Assert.isNotNull(disableProperty);
      this.starterDescriptions = starterDescriptions;
      this.selectedStarterProperty = selectedStarterProperty;
      this.dontAskAgainProperty = dontAskAgainProperty;
      this.disableProperty = disableProperty;
      this.starterPage = new StarterWizardPage<I>("starterPage", starterPageTitle, starterPageDescription, starterDescriptions);
      setWindowTitle(wizardTitle);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      addPage(starterPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPageControls(Composite pageContainer) {
      super.createPageControls(pageContainer);
      StarterPreferenceUtil.getStore().addPropertyChangeListener(propertyListener);
      updateValues();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      // Remove listener because otherwise the values are updated again in UI
      StarterPreferenceUtil.getStore().removePropertyChangeListener(propertyListener);
      // Update disabled property
      boolean disabled = starterPage.isFunctionalityDisabled();
      StarterPreferenceUtil.getStore().setValue(disableProperty, disabled);
      if (!disabled) {
         // Get selected starter
         selectedStarter = starterPage.getSelectedStarter();
         // Update selected starter property
         String id = selectedStarter != null ? selectedStarter.getId() : null;
         StarterPreferenceUtil.getStore().setValue(selectedStarterProperty, id);
         // Update do not ask again property
         StarterPreferenceUtil.getStore().setValue(dontAskAgainProperty, starterPage.isDontAskAgain());
      }
      return true;
   }

   /**
    * Updates the shown values in {@link #starterPage}.
    */
   protected void updateValues() {
      StarterDescription<I> initiallySelectedStarter = StarterUtil.searchGlobalStarter(starterDescriptions, StarterPreferenceUtil.getStore().getString(selectedStarterProperty));
      if (initiallySelectedStarter == null && !starterDescriptions.isEmpty()) {
         initiallySelectedStarter = starterDescriptions.head();
      }
      starterPage.setSelectedStarter(initiallySelectedStarter);
      starterPage.setDontAskAgain(StarterPreferenceUtil.getStore().getBoolean(dontAskAgainProperty));
      starterPage.setFunctionalityDisabled(StarterPreferenceUtil.getStore().getBoolean(disableProperty));
   }
   
   /**
    * Returns the selected {@link StarterDescription}.
    * @return The selected {@link StarterDescription}.
    */
   public StarterDescription<I> getSelectedStarter() {
      return selectedStarter;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      StarterPreferenceUtil.getStore().removePropertyChangeListener(propertyListener);
      super.dispose();
   }

   /**
    * Opens the wizard.
    * @param parentShell The parent {@link Shell}.
    * @param wizardTitle The wizard title.
    * @param starterPageTitle The starter page title.
    * @param starterPageDescription The starter page description.
    * @param starterDescriptions The available {@link StarterDescription}s.
    * @param selectedStarterProperty The property to store the selected {@link StarterDescription} in {@link StarterPreferenceUtil#getStore()}.
    * @param dontAskAgainProperty The property with the do not ask again option in {@link StarterPreferenceUtil#getStore()}.
    * @param disableProperty The property with the disabled option in {@link StarterPreferenceUtil#getStore()}.
    * @return The selected {@link StarterDescription} or {@code null} if not available.
    */
   public static <I> StarterDescription<I> openWizard(Shell parentShell,
                                                      String wizardTitle,
                                                      String starterPageTitle,
                                                      String starterPageDescription,
                                                      ImmutableList<StarterDescription<I>> starterDescriptions,
                                                      String selectedStarterProperty,
                                                      String dontAskAgainProperty,
                                                      String disableProperty) {
      Assert.isNotNull(starterDescriptions);
      Assert.isNotNull(selectedStarterProperty);
      Assert.isNotNull(dontAskAgainProperty);
      Assert.isNotNull(disableProperty);
      // Check if functionality is enabled
      if (!StarterPreferenceUtil.getStore().getBoolean(disableProperty) && !starterDescriptions.isEmpty()) {
         // Compute initiallySelectedStarter
         StarterDescription<I> initiallySelectedStarter = StarterUtil.searchGlobalStarter(starterDescriptions, StarterPreferenceUtil.getStore().getString(selectedStarterProperty));
         // Check if starter can be returned directly without opening the wizard
         if (initiallySelectedStarter != null && StarterPreferenceUtil.getStore().getBoolean(dontAskAgainProperty)) {
            return initiallySelectedStarter;
         }
         else {
            if (initiallySelectedStarter == null && !starterDescriptions.isEmpty()) {
               initiallySelectedStarter = starterDescriptions.head();
            }
            // Create wizard and open in dialog
            StarterWizard<I> wizard = new StarterWizard<I>(wizardTitle, 
                                                           starterPageTitle, 
                                                           starterPageDescription, 
                                                           starterDescriptions, 
                                                           selectedStarterProperty, 
                                                           dontAskAgainProperty, 
                                                           disableProperty);
            WizardDialog dialog = new WizardDialog(parentShell, wizard);
            dialog.setHelpAvailable(false);
            if (dialog.open() == WizardDialog.OK) {
               return wizard.getSelectedStarter();
            }
            else {
               return null;
            }
         }
      }
      else {
         return null;
      }
   }
}