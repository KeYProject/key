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

package org.key_project.sed.ui.visualization.launch;

import java.util.Collections;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.ui.visualization.execution_tree.util.ExecutionTreeUtil;
import org.key_project.sed.ui.visualization.util.LogUtil;
import org.key_project.sed.ui.visualization.util.SETFileLaunchUtil;
import org.key_project.sed.ui.visualization.util.VisualizationImages;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.FileExtensionViewerFilter;

/**
 * {@link AbstractLaunchConfigurationTab} implementation for the
 * Symbolic Execution Debugger based on SET files.
 * @author Martin Hentschel
 */
public class SETFileLaunchConfigurationTab extends AbstractLaunchConfigurationTab {
   /**
    * The {@link Text} to define the path.
    */
   private Text fileText;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      setControl(root);
      root.setLayout(new GridLayout(1, false));
      Group fileGroup = new Group(root, SWT.NONE);
      fileGroup.setText("Existing *." + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION + " file");
      fileGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      fileGroup.setLayout(new GridLayout(3, false));
      Label fileLabel = new Label(fileGroup, SWT.NONE);
      fileLabel.setText("&File");
      fileText = new Text(fileGroup, SWT.BORDER);
      fileText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      fileText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updateLaunchConfigurationDialog();
         }
      });
      Button browseButton = new Button(fileGroup, SWT.PUSH);
      browseButton.setText("&Browse");
      browseButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            browseSetFile();
         }
      });
   }
   
   /**
    * Opens a dialog to select a *.proof file.
    */
   public void browseSetFile() {
      IFile selectedFile = getSetFile();
      IFile[] files = WorkbenchUtil.openFileSelection(getShell(), 
                                                      "File Selection", 
                                                      "Select a *." + ExecutionTreeUtil.DOMAIN_FILE_EXTENSION + " file.", 
                                                      false, 
                                                      selectedFile != null && selectedFile.exists() ? new Object[] {selectedFile} : null, 
                                                      Collections.singleton(new FileExtensionViewerFilter(true, new String[] {ExecutionTreeUtil.DOMAIN_FILE_EXTENSION})));
      if (files != null && files.length == 1) {
         fileText.setText(files[0].getFullPath().toString());
      }
   }
   
   /**
    * Returns the selected set file.
    * @return The selected set file.
    */
   protected IFile getSetFile() {
      try {
         String selectedText = fileText.getText();
         IFile selectedFile = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(selectedText));
         if (selectedFile != null && selectedFile.exists()) {
            return selectedFile;
         }
         else {
            return null;
         }
      }
      catch (Exception e) {
         return null;
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isValid(ILaunchConfiguration launchConfig) {
      if (getSetFile() != null) {
         setErrorMessage(null);
         return true;
      }
      else {
         setErrorMessage("No existing file selected.");
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeFrom(ILaunchConfiguration configuration) {
      try {
         SWTUtil.setText(fileText, SETFileLaunchUtil.getFileToLoadValue(configuration));
      }
      catch (CoreException e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void performApply(ILaunchConfigurationWorkingCopy configuration) {
      configuration.setAttribute(SETFileLaunchUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD, fileText.getText());
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
   public String getName() {
      return "Main";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage() {
      return VisualizationImages.getImage(VisualizationImages.SET_FILE);
   }
}