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

package org.key_project.key4eclipse.resources.ui.propertypages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.ui.IPackagesViewPart;
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
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.navigator.CommonViewer;
import org.key_project.key4eclipse.common.ui.property.AbstractProjectPropertyPage;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;

public class ProofManagementPropertyPage extends AbstractProjectPropertyPage {
   
   private Button enableKeYResourcesBuildsButton;
   
   private Button enableBuildOnStartupButton;

   private Button enableBuildRequiredProofsOnlyButton;
   
   private Button enableAutoInterruptBuildButton;
   
   private Spinner numberOfThreadsSpinner;
   
   private Text numberOfThreadsText;
   
   private Button enableMultiThreadingButton;
   
   private Button autoDeleteProofFilesButton;
   
   private Button hideMefaFilesButton;
   
   private Text fillText;

   
   private SelectionListener buildProofButtonSelectionListener = new SelectionListener() {
      
      @Override
      public void widgetSelected(SelectionEvent e) {
         boolean selected = enableKeYResourcesBuildsButton.getSelection();
         enableBuildOnStartupButton.setEnabled(selected);
         enableBuildRequiredProofsOnlyButton.setEnabled(selected);
         enableAutoInterruptBuildButton.setEnabled(selected);
         enableMultiThreadingButton.setEnabled(selected);
         numberOfThreadsText.setEnabled(selected);
         numberOfThreadsSpinner.setEnabled(selected);
         autoDeleteProofFilesButton.setEnabled(selected);
      }
      
      @Override
      public void widgetDefaultSelected(SelectionEvent e) {
         
      }
   };
   
   
   private SelectionListener enableMultiThreadingButtonSelectionListener = new SelectionListener() {
      
      @Override
      public void widgetSelected(SelectionEvent e) {
         boolean selected = enableMultiThreadingButton.getSelection();
         numberOfThreadsText.setEnabled(selected);
         numberOfThreadsSpinner.setEnabled(selected); 
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

      enableKeYResourcesBuildsButton = new Button(root, SWT.CHECK);
      enableKeYResourcesBuildsButton.setText("Enable KeY Resources builds");
      enableKeYResourcesBuildsButton.addSelectionListener(buildProofButtonSelectionListener);
      setSelectionForKeYResourcesBuildsButton();
      
      Group builderSettings = new Group(root, SWT.NONE);
      builderSettings.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      builderSettings.setLayout(new GridLayout(1, false));
      builderSettings.setText("Builder settings");
      Composite builderSettingsComposite = new Composite(builderSettings, SWT.NONE);
      builderSettingsComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      builderSettingsComposite.setLayout(new GridLayout(1, false));

      enableBuildOnStartupButton = new Button(builderSettingsComposite, SWT.CHECK);
      enableBuildOnStartupButton.setText("Start builds on startup");
      setSelectionForEnableBuildOnStartupButton();
      setEnabledForBuildOnStartupButton();
      
      enableBuildRequiredProofsOnlyButton = new Button(builderSettingsComposite, SWT.CHECK);
      enableBuildRequiredProofsOnlyButton.setText("Build required proofs only");
      setSelectionForEnableBuildRequiredProofsOnlyButton();
      setEnabledForBuildProofsEfficientButton();
      
      enableAutoInterruptBuildButton = new Button(builderSettingsComposite, SWT.CHECK);
      enableAutoInterruptBuildButton.setText("Automatically interrupt and restart build");
      setSelectionForEnableBuildJobButton();
      setEnabledForBuildJobButton();
      
      Group multiThreadingSettings = new Group(builderSettingsComposite, SWT.NONE);
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
      setEnabledForEnableMultiThreadingButton();
      
      fillText = new Text(multiThreadingComposite, SWT.SINGLE);
      fillText.setText("");
      Display display = Display.getCurrent();
      Color backgroundColor = display.getSystemColor(SWT.COLOR_WIDGET_BACKGROUND);
      fillText.setBackground(backgroundColor);
      
      numberOfThreadsText = new Text(multiThreadingComposite, SWT.SINGLE);
      numberOfThreadsText.setText("Number of threads:");
      numberOfThreadsText.setBackground(backgroundColor);

      numberOfThreadsSpinner = new Spinner(multiThreadingComposite, SWT.NONE);
      numberOfThreadsSpinner.setMinimum(1);
      numberOfThreadsSpinner.setMaximum(100);
      numberOfThreadsSpinner.setIncrement(1);
      setSelectionForSetNumberOfThreads();
      setEnabledForSetNumberOfThreads();
      

      autoDeleteProofFilesButton = new Button(builderSettingsComposite, SWT.CHECK);
      autoDeleteProofFilesButton.setText("Delete unnecessary proof files automatically");
      setSelectionForAutoDeleteProofFilesButton();
      setEnabledForAutoDeleteProofFilesButton();
      
      Group folderSettings = new Group(root, SWT.NONE);
      folderSettings.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      folderSettings.setLayout(new GridLayout(1, false));
      folderSettings.setText("Proof folder settings");
      Composite folderSettingsComposite = new Composite(folderSettings, SWT.NONE);
      folderSettingsComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      folderSettingsComposite.setLayout(new GridLayout(1, false));
            
      hideMefaFilesButton = new Button(folderSettingsComposite, SWT.CHECK);
      hideMefaFilesButton.setText("Hide meta files");
      setSelectionForHideMetaFilesButton();
      
      return root;
   }
   
   
   private void setSelectionForKeYResourcesBuildsButton(){
      enableKeYResourcesBuildsButton.setSelection(KeYProjectProperties.isEnableKeYResourcesBuilds(getProject()));    
   }
   
   
   /**
    * Sets the selection for the EnableEfficientProofManagementButton CheckBox.
    */
   private void setSelectionForEnableBuildOnStartupButton(){
      enableBuildOnStartupButton.setSelection(KeYProjectProperties.isEnableBuildOnStartup(getProject()));
      
   }
   
   
   private void setEnabledForBuildOnStartupButton(){
      enableBuildOnStartupButton.setEnabled(enableKeYResourcesBuildsButton.getSelection());
   }

   
   /**
    * Sets the selection for the EnableEfficientProofManagementButton CheckBox.
    */
   private void setSelectionForEnableBuildRequiredProofsOnlyButton(){
      enableBuildRequiredProofsOnlyButton.setSelection(KeYProjectProperties.isEnableBuildRequiredProofsOnly(getProject()));
      
   }
   
   
   private void setEnabledForBuildProofsEfficientButton(){
      enableBuildRequiredProofsOnlyButton.setEnabled(enableKeYResourcesBuildsButton.getSelection());
   }
   
   
   /**
    * Sets the selection for the EnableBuildJobButton CheckBox.
    */
   private void setSelectionForEnableBuildJobButton(){
      enableAutoInterruptBuildButton.setSelection(KeYProjectProperties.isEnableAutoInterruptBuild(getProject()));
   }
   
   
   private void setEnabledForBuildJobButton(){
      enableAutoInterruptBuildButton.setEnabled(enableKeYResourcesBuildsButton.getSelection());
   }
   
   
   /**
    * Sets the selection for the EnableMultiThreadingButton CheckBox.
    */
   private void setSelectionForEnableMultiThreadingButton(){
      enableMultiThreadingButton.setSelection(KeYProjectProperties.isEnableMultiThreading(getProject()));
   }
   
   
   private void setEnabledForEnableMultiThreadingButton(){
      enableMultiThreadingButton.setEnabled(enableKeYResourcesBuildsButton.getSelection());
   }
   
   
   
   /**
    * Sets the selection for the setNumberOfThreads DropDown Menu.
    */
   private void setSelectionForSetNumberOfThreads(){
      int index = KeYProjectProperties.getNumberOfThreads(getProject());
      if(index < 0 || index > 100){
         numberOfThreadsSpinner.setSelection(1);
      }
      else{
         numberOfThreadsSpinner.setSelection(index);
      }
   }
   
   private void setEnabledForSetNumberOfThreads(){
      numberOfThreadsSpinner.setEnabled(enableMultiThreadingButton.isEnabled() && enableMultiThreadingButton.getSelection());
   }
   

   /**
    * Sets the selection for the AutoDeleteProofFilesButton CheckBox.
    */
   private void setSelectionForAutoDeleteProofFilesButton(){
      autoDeleteProofFilesButton.setSelection(KeYProjectProperties.isAutoDeleteProofFiles(getProject()));
   }
   
   
   private void setEnabledForAutoDeleteProofFilesButton(){
      autoDeleteProofFilesButton.setEnabled(enableKeYResourcesBuildsButton.getSelection());
   }
   
   
   /**
    * Sets the selection for the HideMetaFilesButton CheckBox.
    */
   private void setSelectionForHideMetaFilesButton(){
      IProject project = getProject();
      hideMefaFilesButton.setSelection(KeYProjectProperties.isHideMetaFiles(project));
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performOk() {
      try {
         IProject project = getProject();
         KeYProjectProperties.setEnableKeYResourcesBuilds(project, enableKeYResourcesBuildsButton.getSelection());
         KeYProjectProperties.setEnableBuildOnStartup(project, enableBuildOnStartupButton.getSelection());
         KeYProjectProperties.setEnableBuildProofsEfficient(project, enableBuildRequiredProofsOnlyButton.getSelection());
         KeYProjectProperties.setEnableAutoInterruptBuild(project, enableAutoInterruptBuildButton.getSelection());
         KeYProjectProperties.setEnableMultiThreading(project, enableMultiThreadingButton.getSelection());
         KeYProjectProperties.setNumberOfThreads(project, String.valueOf(numberOfThreadsSpinner.getSelection()));
         KeYProjectProperties.setAutoDeleteProofFiles(project, autoDeleteProofFilesButton.getSelection());
         KeYProjectProperties.setHideMetaFiles(project, hideMefaFilesButton.getSelection());
         updateNavigators();
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
      enableKeYResourcesBuildsButton.setSelection(true);
      enableBuildOnStartupButton.setSelection(true);
      enableBuildRequiredProofsOnlyButton.setSelection(true);
      enableAutoInterruptBuildButton.setSelection(true);
      enableMultiThreadingButton.setSelection(true);
      numberOfThreadsSpinner.setSelection(2);
      autoDeleteProofFilesButton.setSelection(true);
      hideMefaFilesButton.setSelection(false);
      super.performDefaults();
   }
   
   
   private void updateNavigators() {
      IWorkbenchPage activePage = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
      IViewPart packageExplorer = activePage.findView("org.eclipse.jdt.ui.PackageExplorer");
      if(packageExplorer != null && packageExplorer instanceof IPackagesViewPart){
         ((IPackagesViewPart) packageExplorer).getTreeViewer().refresh();
      }
      IViewPart projectExplorer = activePage.findView("org.eclipse.ui.navigator.ProjectExplorer");
      if(projectExplorer != null && projectExplorer instanceof CommonNavigator){
         CommonViewer viewer = ((CommonNavigator) projectExplorer).getCommonViewer();
         if(viewer != null){
            viewer.refresh();
         }
      }
   }
}
