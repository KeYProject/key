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

package org.key_project.key4eclipse.common.ui.property;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.viewers.Viewer;
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
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PropertyPage;
import org.key_project.key4eclipse.common.ui.composite.ManageKeYClassPathComposite;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry.KeYPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.util.eclipse.ProjectViewFilter;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;

/**
 * Provides the {@link PropertyPage} that is used to configure KeY specific
 * settings of an {@link IProject}.
 * @author Martin Hentschel
 */
public class KeYProjectPropertyPage extends AbstractProjectPropertyPage {
    /**
     * Radio button to use default key boot class path.
     */
    private Button useDefaultBootClassPathButton;

    /**
     * Radio button to use workspace boot class path.
     */
    private Button useWorkspaceBootClassPathButton;

    /**
     * Radio button to use external boot class path.
     */
    private Button useExternalBootClassPathButton;
    
    /**
     * Shows the custom boot class path.
     */
    private Text bootClassPathText;
    
    /**
     * Opens a dialog to select a custom boot class path.
     */
    private Button selectBootClassPathButton;
    
    /**
     * Allows to manage {@link KeYPathEntry}s.
     */
    private ManageKeYClassPathComposite classPathComposite;
    
    /**
     * The previously selected {@link UseBootClassPathKind}.
     */
    private UseBootClassPathKind oldUseKind;
    
    /**
     * The previously defined workspace boot class path.
     */
    private String oldWorkspaceBootPath;
    
    /**
     * The previously defined external boot class path.
     */
    private String oldExternalBootPath;
    
    /**
     * The source location to load in KeY.
     */
    private Text sourceClassPathText;
    
    /**
     * {@link Button} to browse the source class path
     */
    private Button selectSourceClassPath;
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Control createContents(Composite parent) {
        initializeDialogUnits(parent);
        Composite root = new Composite(parent, SWT.NONE);
        root.setLayout(createGridLayout(1, false));
        // source class path
        Group sourceClassPathGroup = new Group(root, SWT.NONE);
        sourceClassPathGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        sourceClassPathGroup.setLayout(new GridLayout(2, false));
        sourceClassPathGroup.setText("Source class path");
        sourceClassPathText = new Text(sourceClassPathGroup, SWT.BORDER);
        sourceClassPathText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        sourceClassPathText.addModifyListener(new ModifyListener() {
           @Override
           public void modifyText(ModifyEvent e) {
               updateValidState();
           }
        });
        selectSourceClassPath = new Button(sourceClassPathGroup, SWT.PUSH);
        selectSourceClassPath.setText("&...");
        selectSourceClassPath.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                selectSourceClassPath();
            }
        });        
        // boot class path
        Group bootClassPathGroup = new Group(root, SWT.NONE);
        bootClassPathGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        bootClassPathGroup.setLayout(new GridLayout(1, false));
        bootClassPathGroup.setText("Boot class path");
        Composite useBootClassPathComposite = new Composite(bootClassPathGroup, SWT.NONE);
        useBootClassPathComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        useBootClassPathComposite.setLayout(createGridLayout(3, false));
        useDefaultBootClassPathButton = new Button(useBootClassPathComposite, SWT.RADIO);
        useDefaultBootClassPathButton.setText("Use &KeY default");
        useDefaultBootClassPathButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                handleUseBootClassPathChanged();
            }
        });
        useWorkspaceBootClassPathButton = new Button(useBootClassPathComposite, SWT.RADIO);
        useWorkspaceBootClassPathButton.setText("Use directory in &workspace");
        useWorkspaceBootClassPathButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                handleUseBootClassPathChanged();
            }
        });
        useExternalBootClassPathButton = new Button(useBootClassPathComposite, SWT.RADIO);
        useExternalBootClassPathButton.setText("Use &external directory in file system");
        useExternalBootClassPathButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                handleUseBootClassPathChanged();
            }
        });
        Composite bootClassPathComposite = new Composite(bootClassPathGroup, SWT.NONE);
        bootClassPathComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        bootClassPathComposite.setLayout(createGridLayout(3, false));
        Label bootClassPathLabel = new Label(bootClassPathComposite, SWT.NONE);
        bootClassPathLabel.setText("Custom &boot class path");
        bootClassPathText = new Text(bootClassPathComposite, SWT.BORDER);
        bootClassPathText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        bootClassPathText.addModifyListener(new ModifyListener() {
            @Override
            public void modifyText(ModifyEvent e) {
                updateValidState();
            }
        });
        selectBootClassPathButton = new Button(bootClassPathComposite, SWT.PUSH);
        selectBootClassPathButton.setText("...");
        selectBootClassPathButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                selectBootClassPath();
            }
        });
        // class path
        classPathComposite = new ManageKeYClassPathComposite(root, SWT.NONE, "Class path", true, true, "jar");
        classPathComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
        classPathComposite.addPropertyChangeListener(ManageKeYClassPathComposite.PROP_CLASS_PATH_ENTRIES, new PropertyChangeListener() {
           @Override
           public void propertyChange(PropertyChangeEvent evt) {
              updateValidState();
           }
        });
        // Initialize UI controls
        try {
            IProject project = getProject();
            if (project != null) {
                SWTUtil.setText(sourceClassPathText, KeYResourceProperties.getSourceClassPath(project));
                setUseKind(KeYResourceProperties.getUseBootClassPathKind(project));
                SWTUtil.setText(bootClassPathText, KeYResourceProperties.getBootClassPath(project));
                classPathComposite.setClassPathEntries(KeYResourceProperties.getClassPathEntries(project));
                setEnabled(true);
            }
            else {
                setEnabled(false);
            }
        }
        catch (CoreException e) {
            LogUtil.getLogger().logError(e);
            setEnabled(false);
        }
        finally {
            updateValidState();
        }
        return root;
    }

   /**
     * Creates a {@link GridLayout} instance with default settings.
     * @param numColumns The number of columns.
     * @param makeColumnsEqualWidt Make columns equal width.
     * @return The created {@link GridLayout}.
     */
    public static GridLayout createGridLayout(int numColumns, boolean makeColumnsEqualWidt) {
        GridLayout layout = new GridLayout(numColumns, makeColumnsEqualWidt);
        layout.marginWidth = 0;
        layout.marginHeight = 0;
        return layout;
    }

    /**
     * Updates the valid state.
     */
    protected void updateValidState() {
        boolean valid = true;
        // Check source path
        if (valid) {
           String text = sourceClassPathText.getText();
           if (StringUtil.isTrimmedEmpty(text)) {
              valid = false;
              setErrorMessage("No source class path defined.");
           }
           else {
              IResource sourcePath = ResourcesPlugin.getWorkspace().getRoot().findMember(new Path(text));
              if (sourcePath == null || !sourcePath.exists()) {
                 valid = false;
                 setErrorMessage("No existing source path defined.");
              }
              else if (!getProject().contains(sourcePath)) {
                 valid = false;
                 setErrorMessage("Source path not contained in project '" + getProject().getName() + "'.");
              }
           }
        }
        // Check boot path
        if (valid) {
           UseBootClassPathKind kind = getUseKind();
           if (UseBootClassPathKind.WORKSPACE.equals(kind)) {
               valid = new KeYPathEntry(KeYPathEntryKind.WORKSPACE, bootClassPathText.getText()).isValid();
               if (!valid) {
                   if (StringUtil.isEmpty(bootClassPathText.getText())) {
                       setErrorMessage("No workspace boot class path defined.");
                   }
                   else {
                       setErrorMessage("The workspace boot class path \"" + bootClassPathText.getText() + "\" don't exist.");
                   }
               }
           }
           else if (UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM.equals(kind)) {
               valid = new KeYPathEntry(KeYPathEntryKind.EXTERNAL_IN_FILE_SYSTEM, bootClassPathText.getText()).isValid();
               if (!valid) {
                   if (StringUtil.isEmpty(bootClassPathText.getText())) {
                       setErrorMessage("No external boot class path defined.");
                   }
                   else {
                       setErrorMessage("The external boot class path \"" + bootClassPathText.getText() + "\" don't exist.");
                   }
               }
           }
        }
        // Validate class paths
        List<KeYPathEntry> classPathEntries = classPathComposite.getClassPathEntries();
        if (valid && classPathEntries != null) {
            Iterator<KeYPathEntry> iter = classPathEntries.iterator();
            while (valid && iter.hasNext()) {
                KeYPathEntry next = iter.next();
                if (!next.isValid()) {
                    valid = false;
                    setErrorMessage("The class path entry \"" + next.getPath() + "\" refers to a not existing " + (KeYPathEntryKind.WORKSPACE.equals(next.getKind()) ? "workspace resource" : "external resource") + ".");
                }
            }
        }
        // Update valid state
        setValid(valid);
        if (valid) {
            setErrorMessage(null);
        }
    }

    /**
     * Opens the dialog to select the source class path.
     */
    public void selectSourceClassPath() {
       try {
          final List<IResource> sourceLocations = JDTUtil.getSourceResources(getProject());
          IResource currentResource = ResourcesPlugin.getWorkspace().getRoot().findMember(new Path(sourceClassPathText.getText()));
          IContainer[] result = WorkbenchUtil.openFolderSelection(getShell(), 
                                                                  "Select source class path", 
                                                                  "Select a folder, project or create a new one.", 
                                                                  false, 
                                                                  new Object[] {currentResource}, 
                                                                  Collections.singleton(new ProjectViewFilter(getProject()) {
                                                                     @Override
                                                                     public boolean select(Viewer viewer, Object parentElement, Object element) {
                                                                        if (super.select(viewer, parentElement, element)) {
                                                                           return isParentOfOrChild((IResource) element);
                                                                        }
                                                                        else {
                                                                           return false;
                                                                        }
                                                                     }
                                                                     
                                                                     protected boolean isParentOfOrChild(IResource element) {
                                                                        boolean accept = false;
                                                                        Iterator<IResource> iter = sourceLocations.iterator();
                                                                        while (!accept && iter.hasNext()) {
                                                                           IResource next = iter.next();
                                                                           if (element.contains(next) || next.contains(element)) {
                                                                              accept = true;
                                                                           }
                                                                        }
                                                                        return accept;
                                                                     }
                                                                  }));
          if (result != null && result.length == 1) {
             sourceClassPathText.setText(result[0].getFullPath().toString());
          }
      }
      catch (JavaModelException e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(getShell(), e);
      }
    }

   /**
     * Opens the dialog to select the boot class path.
     */
    public void selectBootClassPath() {
        if (useWorkspaceBootClassPathButton.getSelection()) {
            IResource currentResource = ResourcesPlugin.getWorkspace().getRoot().findMember(new Path(bootClassPathText.getText()));
            IContainer[] result = WorkbenchUtil.openFolderSelection(getShell(), 
                                                                    "Select boot class path", 
                                                                    "Select a folder, project or create a new one.", 
                                                                    false, 
                                                                    new Object[] {currentResource}, 
                                                                    null);
            if (result != null && result.length == 1) {
                bootClassPathText.setText(result[0].getFullPath().toString());
            }
        }
        else if (useExternalBootClassPathButton.getSelection()) {
            DirectoryDialog dialog = new DirectoryDialog(getShell());
            dialog.setText("Select boot class path");
            dialog.setMessage("Select a directory or create a new one.");
            dialog.setFilterPath(bootClassPathText.getText());
            String directory = dialog.open();
            if (directory != null) {
                bootClassPathText.setText(directory);
            }
        }
    }

    /**
     * Sets the {@link UseBootClassPathKind} in the UI.
     * @param kind The {@link UseBootClassPathKind} value to show.
     */
    protected void setUseKind(UseBootClassPathKind kind) {
        if (kind != null) {
            useDefaultBootClassPathButton.setSelection(UseBootClassPathKind.KEY_DEFAULT.equals(kind));
            useWorkspaceBootClassPathButton.setSelection(UseBootClassPathKind.WORKSPACE.equals(kind));
            useExternalBootClassPathButton.setSelection(UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM.equals(kind));
        }
        else {
            useDefaultBootClassPathButton.setSelection(true);
            useWorkspaceBootClassPathButton.setSelection(false);
            useExternalBootClassPathButton.setSelection(false);
        }
        handleUseBootClassPathChanged();        
    }
    
    /**
     * Returns the current {@link UseBootClassPathKind}.
     * @return The {@link UseBootClassPathKind} that is shown in the UI.
     */
    protected UseBootClassPathKind getUseKind() {
        if (useWorkspaceBootClassPathButton.getSelection()) {
            return UseBootClassPathKind.WORKSPACE;
        }
        else if (useExternalBootClassPathButton.getSelection()) {
            return UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM;
        }
        else {
            return UseBootClassPathKind.KEY_DEFAULT;
        }
    }
    
    /**
     * When the use boot class path option has changed.
     */
    protected void handleUseBootClassPathChanged() {
        // Update enabled
        bootClassPathText.setEditable(!useDefaultBootClassPathButton.getSelection());
        selectBootClassPathButton.setEnabled(!useDefaultBootClassPathButton.getSelection());
        // Store old boot path
        if (UseBootClassPathKind.WORKSPACE.equals(oldUseKind)) {
            oldWorkspaceBootPath = bootClassPathText.getText();
        }
        else if (UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM.equals(oldUseKind)) {
            oldExternalBootPath = bootClassPathText.getText();
        }
        oldUseKind = getUseKind();
        // Update shown path
        if (UseBootClassPathKind.WORKSPACE.equals(oldUseKind)) {
            SWTUtil.setText(bootClassPathText, oldWorkspaceBootPath);
        }
        else if (UseBootClassPathKind.EXTERNAL_IN_FILE_SYSTEM.equals(oldUseKind)) {
            SWTUtil.setText(bootClassPathText, oldExternalBootPath);
        }
        else {
            SWTUtil.setText(bootClassPathText, null);
        }
    }
    
    /**
     * Enables or disables all UI controls.
     * @param enabled The enabled state to set.
     */
    public void setEnabled(boolean enabled) {
        bootClassPathText.setEditable(enabled && !useDefaultBootClassPathButton.getSelection());
        useDefaultBootClassPathButton.setEnabled(enabled);
        useWorkspaceBootClassPathButton.setEnabled(enabled);
        useExternalBootClassPathButton.setEnabled(enabled);
        selectBootClassPathButton.setEnabled(enabled && !useDefaultBootClassPathButton.getSelection());
        classPathComposite.setEnabled(enabled);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean performOk() {
        try {
            IProject project = getProject();
            KeYResourceProperties.setSourceClassPath(project, sourceClassPathText.getText());
            KeYResourceProperties.setBootClassPath(project, getUseKind(), bootClassPathText.getText());
            KeYResourceProperties.setClassPathEntries(project, classPathComposite.getClassPathEntries());
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
        SWTUtil.setText(sourceClassPathText, KeYResourceProperties.getDefaultSourceClassPath(getProject()));
        setUseKind(UseBootClassPathKind.KEY_DEFAULT);
        SWTUtil.setText(bootClassPathText, null);
        classPathComposite.setClassPathEntries(new LinkedList<KeYPathEntry>());
        super.performDefaults();
    }
}