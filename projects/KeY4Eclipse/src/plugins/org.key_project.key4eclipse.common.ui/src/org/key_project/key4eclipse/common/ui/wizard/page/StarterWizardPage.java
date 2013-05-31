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

package org.key_project.key4eclipse.common.ui.wizard.page;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Link;
import org.eclipse.swt.widgets.Text;
import org.key_project.key4eclipse.common.ui.preference.page.StarterPreferencePage;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;
import org.key_project.key4eclipse.common.ui.provider.StarterDescriptionLabelProvider;
import org.key_project.key4eclipse.common.ui.util.StarterDescription;
import org.key_project.key4eclipse.common.ui.wizard.StarterWizard;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.collection.ImmutableList;

/**
 * {@link WizardPage} used in {@link StarterWizard} to select a {@link StarterDescription}.
 * @author Martin Hentschel
 */
public class StarterWizardPage<I> extends WizardPage {
   /**
    * The available {@link StarterDescription}s as input of {@link #starterViewer}.
    */
   private ImmutableList<StarterDescription<I>> starterDescriptions;
   
   /**
    * Shows the available {@link StarterDescription}s.
    */
   private ListViewer starterViewer;
   
   /**
    * The used {@link ILabelProvider} of {@link #starterViewer}.
    */
   private StarterDescriptionLabelProvider labelProvider;
   
   /**
    * Shows the description of the selected {@link StarterDescription}.
    */
   private Text descriptionText;
   
   /**
    * The do not ask again {@link Button}.
    */
   private Button dontAskAgainButton;
   
   /**
    * The disable {@link Button}.
    */
   private Button disableButton;

   /**
    * Constructor.
    * @param pageName The name of this page.
    * @param title The title of this page.
    * @param description The description of this page.
    * @param starterDescriptions the available {@link StarterDescription}.
    */
   public StarterWizardPage(String pageName, 
                            String title, 
                            String description, 
                            ImmutableList<StarterDescription<I>> starterDescriptions) {
      super(pageName);
      Assert.isNotNull(starterDescriptions);
      this.starterDescriptions = starterDescriptions;
      setTitle(title);
      setDescription(description);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite rootComposite = new Composite(parent, SWT.NONE);
      rootComposite.setLayout(new GridLayout(1, false));
      
      Composite viewerComposite = new Composite(rootComposite, SWT.NONE);
      viewerComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      viewerComposite.setLayout(new GridLayout(2, false));
      
      Group viewerGroup = new Group(viewerComposite, SWT.NONE);
      viewerGroup.setText("Applications");
      viewerGroup.setLayout(new FillLayout());
      viewerGroup.setLayoutData(new GridData(GridData.FILL_VERTICAL));
      starterViewer = new ListViewer(viewerGroup, SWT.BORDER | SWT.SINGLE);
      starterViewer.setContentProvider(ImmutableCollectionContentProvider.getInstance());
      starterViewer.addSelectionChangedListener(new ISelectionChangedListener() {
         @Override
         public void selectionChanged(SelectionChangedEvent event) {
            updatePageCompletedAndShownDescription();
         }
      });
      labelProvider = new StarterDescriptionLabelProvider();
      starterViewer.setLabelProvider(labelProvider);
      starterViewer.setInput(starterDescriptions);
      
      Group descriptionGroup = new Group(viewerComposite, SWT.NONE);
      GridData descriptionGroupData = new GridData(GridData.FILL_BOTH);
      descriptionGroupData.widthHint = 400;
      descriptionGroup.setLayoutData(descriptionGroupData);
      descriptionGroup.setText("Description");
      descriptionGroup.setLayout(new FillLayout());
      descriptionText = new Text(descriptionGroup, SWT.BORDER | SWT.V_SCROLL | SWT.MULTI | SWT.WRAP);
      descriptionText.setEditable(false);
      
      Composite disableComposite = new Composite(rootComposite, SWT.NONE);
      disableComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      disableComposite.setLayout(new GridLayout(4, false));

      dontAskAgainButton = new Button(disableComposite, SWT.CHECK);
      dontAskAgainButton.setText("&Do not ask again");

      disableButton = new Button(disableComposite, SWT.CHECK);
      disableButton.setText("D&isable functionality");
      disableButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            updateEnablement();
         }
      });
      Label emptyLabel = new Label(disableComposite, SWT.NONE);
      emptyLabel.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      Link preferenceLink = new Link(disableComposite, SWT.NONE);
      preferenceLink.setText("Can be changed later in the <a>Preferences</a>");
      preferenceLink.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            openPreferencePage();
         }
      });
      
      setControl(rootComposite);
      updatePageCompletedAndShownDescription();
      updateEnablement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (labelProvider != null) {
         labelProvider.dispose();
      }
      super.dispose();
   }

   /**
    * Updates the enabled state of the other controls based on the selection
    * of {@link #disableButton}.
    */
   protected void updateEnablement() {
      boolean disabled = isFunctionalityDisabled();
      starterViewer.getList().setEnabled(!disabled);
      dontAskAgainButton.setEnabled(!disabled);
      descriptionText.setEnabled(!disabled);
   }

   /**
    * Updates the page completed state and the shown description when
    * the selected {@link StarterDescription} has changed.
    */
   protected void updatePageCompletedAndShownDescription() {
      StarterDescription<I> selectedStarter = getSelectedStarter();
      if (selectedStarter != null) {
         // Update page completed state
         setPageComplete(true);
         // Update shown description
         SWTUtil.setText(descriptionText, selectedStarter.getDescription());
      }
      else {
         // Update page completed state
         setPageComplete(isFunctionalityDisabled());
         // Update shown description
         descriptionText.setText(StringUtil.EMPTY_STRING);
      }
   }

   /**
    * Opens the preference page.
    */
   protected void openPreferencePage() {
      StarterPreferencePage.openPreferencePage(getShell());
   }
   
   /**
    * Returns the selected {@link StarterDescription}.
    * @return The selected {@link StarterDescription}.
    */
   @SuppressWarnings("unchecked")
   public StarterDescription<I> getSelectedStarter() {
      Object selected = SWTUtil.getFirstElement(starterViewer.getSelection());
      if (selected instanceof StarterDescription) {
         return (StarterDescription<I>)selected;
      }
      else {
         return null;
      }
   }
   
   /**
    * Sets the selected {@link StarterDescription}.
    * @param toSelect The {@link StarterDescription} to select.
    */
   public void setSelectedStarter(StarterDescription<I> toSelect) {
      starterViewer.setSelection(SWTUtil.createSelection(toSelect));
   }
   
   /**
    * Checks if the do not ask again option is enabled or not.
    * @return {@code true} don't ask again, {@code false} ask again.
    */
   public boolean isDontAskAgain() {
      return dontAskAgainButton.getSelection();
   }
   
   /**
    * Sets the don't ask again option.
    * @param dontAsk don't ask again, {@code false} ask again.
    */
   public void setDontAskAgain(boolean dontAsk) {
      dontAskAgainButton.setSelection(dontAsk);
   }
   
   /**
    * Checks if the whole functionality is disabled or not.
    * @return {@code true} disabled, {@code false} enabled.
    */
   public boolean isFunctionalityDisabled() {
      return disableButton.getSelection();
   }
   
   /**
    * Sets the disabled flag.
    * @param disabled {@code true} disabled, {@code false} enabled.
    */
   public void setFunctionalityDisabled(boolean disabled) {
      disableButton.setSelection(disabled);
      updateEnablement();
   }
}