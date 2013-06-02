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

package org.key_project.key4eclipse.resources.ui.propertypages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.key_project.key4eclipse.common.ui.property.AbstractProjectPropertyPage;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.ui.util.KeY4EclipseResourcesUiUtil;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;

public class ProofManagementPropertyPage extends AbstractProjectPropertyPage {
   
   private Button buildProofButton;

   private Button enableEfficentProofManagementButton;
   
   private Button autoDeleteProofFilesButton;
   
   private Button hideMefaFiles;
   
   private SelectionListener buildProofButtonSelectionListener = new SelectionListener() {
      
      @Override
      public void widgetSelected(SelectionEvent e) {
         boolean isSelected = buildProofButton.getSelection();
         if(isSelected){
            enableEfficentProofManagementButton.setEnabled(true);
         }
         else{
            enableEfficentProofManagementButton.setEnabled(false);
         }
         
      }
      
      @Override
      public void widgetDefaultSelected(SelectionEvent e) {
         System.out.println("widgetDefaultSelected");
      }
   };

   
   /**
    * {@inheritDoc}
    */
   @Override
   protected Control createContents(Composite parent) {
      initializeDialogUnits(parent);
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(1, false));
      
      Group builderSettings = new Group(root, SWT.NONE);
      builderSettings.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      builderSettings.setLayout(new GridLayout(1, false));
      builderSettings.setText("Builder settings");
      Composite builderSettingsComposite = new Composite(builderSettings, SWT.NONE);
      builderSettingsComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      builderSettingsComposite.setLayout(new GridLayout(1, false));
      
      buildProofButton = new Button(builderSettingsComposite, SWT.CHECK);
      buildProofButton.setText("Build proofs");
      buildProofButton.addSelectionListener(buildProofButtonSelectionListener);
      setSelectionForBuildProofsButton();
      
      enableEfficentProofManagementButton = new Button(builderSettingsComposite, SWT.CHECK);
      enableEfficentProofManagementButton.setText("Build proof efficient");
      setSelectionForEnableEfficientProofManagementButton();
      setEnabledForEfficientProfManagement();
      
      Group folderSettings = new Group(root, SWT.NONE);
      folderSettings.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      folderSettings.setLayout(new GridLayout(1, false));
      folderSettings.setText("Proof folder settings");
      Composite folderSettingsComposite = new Composite(folderSettings, SWT.NONE);
      folderSettingsComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      folderSettingsComposite.setLayout(new GridLayout(1, false));
      
      autoDeleteProofFilesButton = new Button(folderSettingsComposite, SWT.CHECK);
      autoDeleteProofFilesButton.setText("Delete unnecessary proof files automatically");
      setSelectionForAutoDeleteProofFilesButton();
      hideMefaFiles = new Button(folderSettingsComposite, SWT.CHECK);
      hideMefaFiles.setText("Hide meta files");
      setSelectionForHideMetaFilesButton();
      
      return root;
   }
   
   
   private void setSelectionForBuildProofsButton(){
      try{
         IProject project = getProject();
         buildProofButton.setSelection(KeYProjectProperties.isBuildProofs(project));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         buildProofButton.setEnabled(false);
      }      
   }

   
   /**
    * Sets the selection for the EnableEfficientProofManagementButton CheckBox.
    */
   private void setSelectionForEnableEfficientProofManagementButton(){
      try {
         IProject project = getProject();
         enableEfficentProofManagementButton.setSelection(KeYProjectProperties.isEnableEfficientProofManagement(project));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         enableEfficentProofManagementButton.setEnabled(false);
      }
   }
   
   
   private void setEnabledForEfficientProfManagement(){
      enableEfficentProofManagementButton.setEnabled(buildProofButton.getSelection());
   }
   

   /**
    * Sets the selection for the AutoDeleteProofFilesButton CheckBox.
    */
   private void setSelectionForAutoDeleteProofFilesButton(){
      try {
         IProject project = getProject();
         autoDeleteProofFilesButton.setSelection(KeYProjectProperties.isAutoDeleteProofFiles(project));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         autoDeleteProofFilesButton.setEnabled(false);
      }
   }
   
   
   /**
    * Sets the selection for the HideMetaFilesButton CheckBox.
    */
   private void setSelectionForHideMetaFilesButton(){
      try {
         IProject project = getProject();
         hideMefaFiles.setSelection(KeYProjectProperties.isHideMetaFiles(project));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         hideMefaFiles.setEnabled(false);
      }
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performOk() {
      try {
         IProject project = getProject();
         KeYProjectProperties.setBuildProofs(project, buildProofButton.getSelection());
         KeYProjectProperties.setEnableEfficientProofManagement(project, enableEfficentProofManagementButton.getSelection());
         KeYProjectProperties.setAutoDeleteProofFiles(project, autoDeleteProofFilesButton.getSelection());
         KeYProjectProperties.setHideMetaFiles(project, hideMefaFiles.getSelection());
         KeY4EclipseResourcesUiUtil.hideMetaFiles(project, KeYProjectProperties.isHideMetaFiles(project));
         return super.performOk();
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         return false;
      }
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void performDefaults() {
      buildProofButton.setSelection(true);
      enableEfficentProofManagementButton.setSelection(false);
      autoDeleteProofFilesButton.setSelection(false);
      hideMefaFiles.setSelection(false);
      super.performDefaults();
   }
}
