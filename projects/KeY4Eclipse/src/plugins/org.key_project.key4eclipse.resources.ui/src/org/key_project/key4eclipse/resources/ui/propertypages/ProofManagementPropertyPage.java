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
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Spinner;
import org.eclipse.swt.widgets.Text;
import org.key_project.key4eclipse.common.ui.property.AbstractProjectPropertyPage;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;

public class ProofManagementPropertyPage extends AbstractProjectPropertyPage {
   
   private Button enableBuildProofsButton;

   private Button enableBuildRequiredProofsOnlyButton;
   
   private Spinner setNumberOfThreadsSpinner;
   
   private Text setNumberOfThreadsText;
   
   private Button enableMultiThreadingButton;
   
   private Button autoDeleteProofFilesButton;
   
   private Button hideMefaFiles;
   
   private Text fillText;

   
   private SelectionListener buildProofButtonSelectionListener = new SelectionListener() {
      
      @Override
      public void widgetSelected(SelectionEvent e) {
         boolean isSelected = enableBuildProofsButton.getSelection();
         if(isSelected){
            enableBuildRequiredProofsOnlyButton.setEnabled(true);
         }
         else{
            enableBuildRequiredProofsOnlyButton.setEnabled(false);
         }
         
      }
      
      @Override
      public void widgetDefaultSelected(SelectionEvent e) {
      }
   };
   
   
private SelectionListener enableMultiThreadingButtonSelectionListener = new SelectionListener() {
      
      @Override
      public void widgetSelected(SelectionEvent e) {
         boolean isSelected = enableMultiThreadingButton.getSelection();
         if(isSelected){
            setNumberOfThreadsSpinner.setEnabled(true);
         }
         else{
            setNumberOfThreadsSpinner.setEnabled(false);
         }
         
      }

      @Override
      public void widgetDefaultSelected(SelectionEvent e) {
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
      
      enableBuildProofsButton = new Button(builderSettingsComposite, SWT.CHECK);
      enableBuildProofsButton.setText("Build proofs");
      enableBuildProofsButton.addSelectionListener(buildProofButtonSelectionListener);
      setSelectionForBuildProofsButton();
      
      enableBuildRequiredProofsOnlyButton = new Button(builderSettingsComposite, SWT.CHECK);
      enableBuildRequiredProofsOnlyButton.setText("Build required proofs only");
      setSelectionForEnableBuildRequiredProofsOnlyButton();
      setEnabledForBuildProofsEfficientButton();
      
      
      Group multiThreadingSettings = new Group(root, SWT.NONE);
      multiThreadingSettings.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      multiThreadingSettings.setLayout(new GridLayout(1, false));
      multiThreadingSettings.setText("Multi Threading");
      Composite multiThreadingComposite = new Composite(multiThreadingSettings, SWT.NONE);
      multiThreadingComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      multiThreadingComposite.setLayout(new GridLayout(2, false));
      
      enableMultiThreadingButton = new Button(multiThreadingComposite, SWT.CHECK);
      enableMultiThreadingButton.setText("Enable multithreading");
      enableMultiThreadingButton.addSelectionListener(enableMultiThreadingButtonSelectionListener);
      setSelectionForEnableMultiThreadingButton();
      
      fillText = new Text(multiThreadingComposite, SWT.SINGLE);
      fillText.setText("");
      Display display = Display.getCurrent();
      Color backgroundColor = display.getSystemColor(SWT.COLOR_WIDGET_BACKGROUND);
      fillText.setBackground(backgroundColor);
      
      setNumberOfThreadsText = new Text(multiThreadingComposite, SWT.SINGLE);
      setNumberOfThreadsText.setText("Number of threads:");
      setNumberOfThreadsText.setBackground(backgroundColor);

      setNumberOfThreadsSpinner = new Spinner(multiThreadingComposite, SWT.NONE);
      setNumberOfThreadsSpinner.setMinimum(1);
      setNumberOfThreadsSpinner.setMaximum(100);
      setNumberOfThreadsSpinner.setIncrement(1);
      setSelectionForSetNumberOfThreads();
      setEnabledForSetNumberOfThreads();
      
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
      hideMefaFiles.setText("Hide meta files (Refresh the project afterwards)");
      setSelectionForHideMetaFilesButton();
      
      return root;
   }
   
   
   private void setSelectionForBuildProofsButton(){
      try{
         IProject project = getProject();
         enableBuildProofsButton.setSelection(KeYProjectProperties.isEnableBuildProofs(project));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         enableBuildProofsButton.setEnabled(false);
      }      
   }

   
   /**
    * Sets the selection for the EnableEfficientProofManagementButton CheckBox.
    */
   private void setSelectionForEnableBuildRequiredProofsOnlyButton(){
      try {
         IProject project = getProject();
         enableBuildRequiredProofsOnlyButton.setSelection(KeYProjectProperties.isEnableBuildRequiredProofsOnly(project));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         enableBuildRequiredProofsOnlyButton.setEnabled(false);
      }
   }
   
   
   private void setEnabledForBuildProofsEfficientButton(){
      enableBuildRequiredProofsOnlyButton.setEnabled(enableBuildProofsButton.getSelection());
   }
   
   
   /**
    * Sets the selection for the EnableMultiThreadingButton CheckBox.
    */
   private void setSelectionForEnableMultiThreadingButton(){
      try {
         IProject project = getProject();
         enableMultiThreadingButton.setSelection(KeYProjectProperties.isEnableMultiThreading(project));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         enableMultiThreadingButton.setEnabled(false);
      }
   }
   
   
   
   /**
    * Sets the selection for the setNumberOfThreads DropDown Menu.
    */
   private void setSelectionForSetNumberOfThreads(){
      try {
         IProject project = getProject();
         int index = KeYProjectProperties.getNumberOfThreads(project);
         if(index < 0 || index > 100){
            setNumberOfThreadsSpinner.setSelection(1);
         }
         else{
            setNumberOfThreadsSpinner.setSelection(index);
         }
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
         setNumberOfThreadsSpinner.setEnabled(false);
      }
   }
   
   private void setEnabledForSetNumberOfThreads(){
      setNumberOfThreadsSpinner.setEnabled(enableMultiThreadingButton.getSelection());
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
         KeYProjectProperties.setEnableBuildProofs(project, enableBuildProofsButton.getSelection());
         KeYProjectProperties.setEnableBuildProofsEfficient(project, enableBuildRequiredProofsOnlyButton.getSelection());
         KeYProjectProperties.setEnableMultiThreading(project, enableMultiThreadingButton.getSelection());
         KeYProjectProperties.setNumberOfThreads(project, String.valueOf(setNumberOfThreadsSpinner.getSelection()));
         KeYProjectProperties.setAutoDeleteProofFiles(project, autoDeleteProofFilesButton.getSelection());
         KeYProjectProperties.setHideMetaFiles(project, hideMefaFiles.getSelection());
         KeYResourcesUtil.hideMetaFiles(project);
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
      enableBuildProofsButton.setSelection(true);
      enableBuildRequiredProofsOnlyButton.setSelection(true);
      enableMultiThreadingButton.setSelection(true);
      setNumberOfThreadsSpinner.setSelection(2);
      autoDeleteProofFilesButton.setSelection(true);
      hideMefaFiles.setSelection(false);
      super.performDefaults();
   }
}
