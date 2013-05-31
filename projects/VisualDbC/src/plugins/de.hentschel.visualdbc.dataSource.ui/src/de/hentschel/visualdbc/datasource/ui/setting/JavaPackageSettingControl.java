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

package de.hentschel.visualdbc.datasource.ui.setting;

import java.io.File;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
import org.eclipse.emf.common.ui.dialogs.WorkspaceResourceDialog;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.ui.JavaElementLabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.ElementListSelectionDialog;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.jdt.JDTUtil;

import de.hentschel.visualdbc.datasource.ui.setting.event.SettingControlEvent;
import de.hentschel.visualdbc.datasource.ui.util.LogUtil;

/**
 * <p>
 * Implementation of {@link ISettingControl} to define a {@link File} value.
 * </p>
 * <p>
 * The value depends on the selected type:
 * <ul>
 *    <li>Resource: {@link IPath}</li>
 *    <li>Directory: {@link File}</li>
 *    <li>Package: {@link IJavaElement}</li>
 * </ul>
 * </p>
 * @author Martin Hentschel
 */
public class JavaPackageSettingControl extends AbstractSettingControl {
   /**
    * The {@link Text} control to edit the value.
    */
   private Text text;
   
   /**
    * Type: {@link IResource}
    */
   private Button resourceButton;
   
   /**
    * Type: {@link File}
    */
   private Button fileButton;
   
   /**
    * Type: Package in form of {@link IJavaElement}.
    */
   private Button packageButton;

   /**
    * The old selected resource.
    */
   private String oldResource = "";
   
   /**
    * The old selected file.
    */
   private String oldFile = "";
   
   /**
    * The old selected package.
    */
   private IJavaElement oldPackage = null;
   
   /**
    * The old selected {@link Button}.
    */
   private Button lastButton;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Control createControl(Composite parent) {
      Composite rootComposite = new Composite(parent, SWT.NONE);
      GridLayout rootLayout = new GridLayout(1, false);
      rootLayout.marginWidth = 0;
      rootLayout.marginHeight = 0;
      rootComposite.setLayout(rootLayout);
      // Type
      Composite typeComposite = new Composite(rootComposite, SWT.NONE);
      typeComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      GridLayout typeLayout = new GridLayout(3, false);
      typeLayout.marginWidth = 0;
      typeLayout.marginHeight = 0;
      typeComposite.setLayout(typeLayout);
      resourceButton = new Button(typeComposite, SWT.RADIO);
      resourceButton.setText("&Resource");
      resourceButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (resourceButton.getSelection()) {
               handleTypeChange(resourceButton);
            }
         }
      });
      fileButton = new Button(typeComposite, SWT.RADIO);
      fileButton.setText("Director&y");
      fileButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (fileButton.getSelection()) {
               handleTypeChange(fileButton);
            }
         }
      });
      packageButton = new Button(typeComposite, SWT.RADIO);
      packageButton.setText("&Package");
      packageButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            if (packageButton.getSelection()) {
               handleTypeChange(packageButton);
            }
         }
      });
      // Text
      Composite textComposite = new Composite(rootComposite, SWT.NONE);
      textComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      GridLayout textLayout = new GridLayout(2, false);
      textLayout.marginWidth = 0;
      textLayout.marginHeight = 0;
      textComposite.setLayout(textLayout);
      text = new Text(textComposite, SWT.BORDER);
      text.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      text.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            handleTextModified();
         }
      });
      Button selectButton = new Button(textComposite, SWT.PUSH);
      selectButton.setText("&...");
      selectButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            openSelectDialog();
         }
      });
      // Initialize control
      lastButton = resourceButton;
      resourceButton.setSelection(true);
      handleTypeChange(resourceButton);
      return rootComposite;
   }

   /**
    * When the type selection has changed.
    * @param newButton The new selected type {@link Button}.
    */
   protected void handleTypeChange(Button newButton) {
      if (!ObjectUtil.equals(lastButton, newButton)) {
         // Store old value
         if (lastButton.equals(fileButton)) {
            oldFile = text.getText();
         }
         else if (lastButton.equals(packageButton)) {
            // Nothing to do
         }
         else {
            oldResource = text.getText();
         }
         lastButton = newButton;
      }
      // Set new value
      updatePathText(newButton);
   }
   
   protected void updatePathText(Button newButton) {
      if (newButton.equals(fileButton)) {
         text.setText(oldFile);
         text.setEditable(true);
      }
      else if (newButton.equals(packageButton)) {
         text.setText(oldPackage != null ? oldPackage.getElementName() : "");
         text.setEditable(false);
      }
      else {
         text.setText(oldResource);
         text.setEditable(true);
      }
   }

   /**
    * Opens the select directory dialog and changes the selected one
    * if a new one was selected.
    */
   public void openSelectDialog() {
      if (lastButton.equals(fileButton)) {
         openSelectDirectoryDialog();
      }
      else if (lastButton.equals(packageButton)) {
         openSelectPackageButton();
      }
      else {
         openSelectResourceDialog();
      }
   }

   /**
    * Opens the select package dialog.
    */
   protected void openSelectPackageButton() {
      try {
         IJavaElement[] packages = JDTUtil.getAllPackageFragmentRoot();
         ElementListSelectionDialog dialog= new ElementListSelectionDialog(text.getShell(), new JavaElementLabelProvider(JavaElementLabelProvider.SHOW_DEFAULT));
         dialog.setIgnoreCase(false);
         dialog.setTitle("Select package");
         dialog.setMessage("&Choose a package:");
         dialog.setEmptyListMessage("Cannot find packages to select.");
         dialog.setElements(packages);
         dialog.setHelpAvailable(false);
         if (oldPackage != null) {
            dialog.setInitialSelections(new Object[] {oldPackage});
         }
         int result = dialog.open();
         if (result == ElementListSelectionDialog.OK) {
            Object firstResult = dialog.getFirstResult();
            if (firstResult instanceof IJavaElement) {
               oldPackage = (IJavaElement)firstResult;
               text.setText(oldPackage.getElementName());
            }
         }
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * Opens the select resource dialog.
    */
   protected void openSelectResourceDialog() {
      IResource currentResource = ResourcesPlugin.getWorkspace().getRoot().findMember((IPath)getValue());
      IContainer[] result = WorkspaceResourceDialog.openFolderSelection(text.getShell(), 
                                                                        "Select container", 
                                                                        "Select a folder, project or create a new one.", 
                                                                        false, 
                                                                        new Object[] {currentResource}, 
                                                                        null);
      if (result != null && result.length == 1) {
         text.setText(result[0].getFullPath().toString());
      }
   }

   /**
    * Opens the select directory dialog.
    */
   protected void openSelectDirectoryDialog() {
      DirectoryDialog dialog = new DirectoryDialog(text.getShell());
      dialog.setText("Select directory");
      dialog.setMessage("Select a directory or create a new one.");
      dialog.setFilterPath(text.getText());
      String directory = dialog.open();
      if (directory != null) {
         text.setText(directory);
      }
   }

   /**
    * When the text has changed.
    */
   protected void handleTextModified() {
      fireValueChanged(new SettingControlEvent(this, getValue(), getValidationMessage()));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getValue() {
      if (fileButton.getSelection()) {
         return new File(text.getText());
      }
      else if (packageButton.getSelection()) {
         return oldPackage;
      }
      else {
         return new Path(text.getText());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setValue(Object value) {
      if (value instanceof File) {
         setFileValue((File)value);
      }
      else if (value instanceof IResource) {
         setResourceValue((IResource)value);
      }
      else if (value instanceof IJavaElement) {
         setJavaValue((IJavaElement)value);
      }
   }
   
   /**
    * Sets the {@link IJavaElement} value.
    * @param value The {@link IJavaElement} value to set.
    */
   protected void setJavaValue(IJavaElement value) {
      IJavaElement packageElement = JDTUtil.getPackage((IJavaElement)value);
      if (packageElement != null) { // Is null for example if a java project is selected.
         oldPackage = packageElement;
         fileButton.setSelection(false);
         resourceButton.setSelection(false);
         packageButton.setSelection(true);
         lastButton = packageButton;
         updatePathText(packageButton);
         IResource resource = oldPackage.getResource();
         if (resource != null) {
            oldResource = resource.getFullPath().toString();
            File file = ResourceUtil.getLocation(resource);
            if (file != null) {
               oldFile = file.toString();
            }
         }
      }
      else {
         setResourceValue(value.getResource());
      }
   }

   /**
    * Sets the {@link IResource} value.
    * @param value The {@link IResource} value to set.
    */
   protected void setResourceValue(IResource value) {
      fileButton.setSelection(false);
      resourceButton.setSelection(true);
      packageButton.setSelection(false);
      IResource resource = (IResource)value;
      if (resource.getType() == IResource.FILE) {
         resource = resource.getParent();
      }
      oldResource = resource.getFullPath().toString();
      File file = ResourceUtil.getLocation(resource);
      if (file != null) {
         oldFile = file.toString();
      }
      lastButton = resourceButton;
      updatePathText(resourceButton);
   }

   /**
    * Sets the {@link File} value.
    * @param value The {@link File} value to set.
    */
   protected void setFileValue(File value) {
      fileButton.setSelection(true);
      resourceButton.setSelection(false);
      packageButton.setSelection(false);
      oldFile = value.toString();
      lastButton = fileButton;
      updatePathText(fileButton);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getValidationMessage() {
      return getValidationMessage(getValue());
   }

   /**
    * Validates the value.
    * @param value The value to valid.
    * @return The error message or {@code null} if everything is valid.
    */
   protected String getValidationMessage(Object value) {
      if (value instanceof File) {
         if (!((File)value).isDirectory()) {
            return "No existing directory defined.";
         }
      }
      else if (value instanceof IPath) {
         IResource resource = ResourcesPlugin.getWorkspace().getRoot().findMember((IPath)value);
         if (resource != null && !(resource instanceof IWorkspaceRoot)) {
            return getValidationMessage(resource);
         }
         else {
            return "No existing project or folder defined.";
         }
      }
      else if (value instanceof IResource) {
         IResource resource = (IResource)value;
         if (resource == null || !resource.exists() || resource.getType() == IResource.FILE) {
            return "No existing project or folder defined.";
         }
         File resourceLocation = ResourceUtil.getLocation(resource);
         if (resourceLocation == null || !resourceLocation.isDirectory()) {
            return "The resource is not a local directory.";
         }
      }
      else if (value instanceof IJavaElement) {
         IResource resource = ((IJavaElement)value).getResource();
         String resourceMessage = getValidationMessage(resource);
         if (resourceMessage != null) {
            return "No existing package defined.";
         }
      }
      else if (value == null) {
         return "No directory defined.";
      }
      else {
         return "Invalid type.";
      }
      return null; // Return valid
   }
}