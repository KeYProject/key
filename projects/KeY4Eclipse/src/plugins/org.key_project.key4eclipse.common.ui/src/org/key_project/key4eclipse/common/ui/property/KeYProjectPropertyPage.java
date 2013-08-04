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

package org.key_project.key4eclipse.common.ui.property;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
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
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PropertyPage;
import org.key_project.key4eclipse.common.ui.provider.KeYClassPathEntryLabelProvider;
import org.key_project.key4eclipse.common.ui.util.LogUtil;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry.KeYClassPathEntryKind;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties.UseBootClassPathKind;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.FileExtensionViewerFilter;
import org.key_project.util.java.StringUtil;

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
     * Shows all class path entries.
     */
    private TableViewer classPathTableViewer; 
    
    /**
     * Adds a directory class path entry from the workspace.
     */
    private Button addWorkspaceButton;
    
    /**
     * Adds an external directory class path entry.
     */
    private Button addExternalButton;
    
    /**
     * Adds a file class path entry from the workspace.
     */
    private Button addWorkspaceFileButton;
    
    /**
     * Adds an external file class path entry.
     */
    private Button addExternalFileButton;
    
    /**
     * Removes all selected class path entries.
     */
    private Button removeButton;
    
    /**
     * Moves the selected class path entries one up.
     */
    private Button upButton;
    
    /**
     * Moves the selected class path entries one down.
     */
    private Button downButton;
    
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
     * Contains the shown class path entries.
     */
    private List<KeYClassPathEntry> classPathEntries;
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Control createContents(Composite parent) {
        initializeDialogUnits(parent);
        Composite root = new Composite(parent, SWT.NONE);
        root.setLayout(createGridLayout(1, false));
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
        selectBootClassPathButton.setText("&...");
        selectBootClassPathButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                selectBootClassPath();
            }
        });
        // class path
        Group classPathGroup = new Group(root, SWT.NONE);
        classPathGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
        classPathGroup.setLayout(new GridLayout(2, false));
        classPathGroup.setText("Class path");
        Composite classPathComposite = new Composite(classPathGroup, SWT.NONE);
        classPathComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
        classPathComposite.setLayout(createGridLayout(2, false));
        classPathTableViewer = new TableViewer(classPathComposite, SWT.BORDER | SWT.MULTI | SWT.FULL_SELECTION);
        classPathTableViewer.getTable().setLayoutData(new GridData(GridData.FILL_BOTH));
        classPathTableViewer.setContentProvider(ArrayContentProvider.getInstance());
        classPathTableViewer.setLabelProvider(new KeYClassPathEntryLabelProvider());
        classPathTableViewer.addSelectionChangedListener(new ISelectionChangedListener() {
            @Override
            public void selectionChanged(SelectionChangedEvent event) {
                handleClassPathViewerSelectionChanged();
            }
        });
        Composite classPathButtonComposite = new Composite(classPathGroup, SWT.NONE);
        classPathButtonComposite.setLayoutData(new GridData(GridData.BEGINNING, GridData.BEGINNING, false, false));
        classPathButtonComposite.setLayout(createGridLayout(1, true));
        addWorkspaceButton = new Button(classPathButtonComposite, SWT.PUSH);
        addWorkspaceButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        addWorkspaceButton.setText("Add Works&pace");
        addWorkspaceButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                addWorkspaceClassPathEntry();
            }
        });
        addWorkspaceFileButton = new Button(classPathButtonComposite, SWT.PUSH);
        addWorkspaceFileButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        addWorkspaceFileButton.setText("Add Workspace F&ile");
        addWorkspaceFileButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                addWorkspaceFileClassPathEntry();
            }
        });
        addExternalButton = new Button(classPathButtonComposite, SWT.PUSH);
        addExternalButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        addExternalButton.setText("Add Externa&l");
        addExternalButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                addExternalClassPathEntry();
            }
        });
        addExternalFileButton = new Button(classPathButtonComposite, SWT.PUSH);
        addExternalFileButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        addExternalFileButton.setText("Add Exter&nal File");
        addExternalFileButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                addExternalFileClassPathEntry();
            }
        });
        removeButton = new Button(classPathButtonComposite, SWT.PUSH);
        removeButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        removeButton.setText("&Remove");
        removeButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                removeSelectedClassPathEntries();
            }
        });
        upButton = new Button(classPathButtonComposite, SWT.PUSH);
        upButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        upButton.setText("&Up");
        upButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                moveSelectedClassPathEntriesUp();
            }
        });
        downButton = new Button(classPathButtonComposite, SWT.PUSH);
        downButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        downButton.setText("D&own");
        downButton.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
                moveSelectedClassPathEntriesDown();
            }
        });
        // Initialize UI controls
        try {
            IProject project = getProject();
            if (project != null) {
                setUseKind(KeYResourceProperties.getUseBootClassPathKind(project));
                SWTUtil.setText(bootClassPathText, KeYResourceProperties.getBootClassPath(project));
                classPathEntries = KeYResourceProperties.getClassPathEntries(project);
                if (classPathEntries == null) {
                    classPathEntries = new LinkedList<KeYClassPathEntry>();
                }
                updateClassPathViewer();
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
    protected GridLayout createGridLayout(int numColumns, boolean makeColumnsEqualWidt) {
        GridLayout layout = new GridLayout(numColumns, makeColumnsEqualWidt);
        layout.marginWidth = 0;
        layout.marginHeight = 0;
        return layout;
    }

    /**
     * Moves the selected entries one up if possible.
     */
    public void moveSelectedClassPathEntriesDown() {
        ISelection selection = classPathTableViewer.getSelection();
        if (selection instanceof IStructuredSelection) {
            Object[] elements = ((IStructuredSelection)selection).toArray();
            for (int i = elements.length - 1; i >= 0; i--) {
                if (elements[i] instanceof KeYClassPathEntry) {
                    KeYClassPathEntry entry = (KeYClassPathEntry)elements[i];
                    int index = classPathEntries.indexOf(entry);
                    if (index < classPathEntries.size() - 1) {
                        classPathEntries.remove(index);
                        classPathEntries.add(index + 1, entry);
                    }
                }
            }
        }
        updateClassPathViewer();
        classPathTableViewer.setSelection(selection);
    }

    /**
     * Moves the selected entries one down if possible.
     */
    public void moveSelectedClassPathEntriesUp() {
        ISelection selection = classPathTableViewer.getSelection();
        if (selection instanceof IStructuredSelection) {
            Object[] elements = ((IStructuredSelection)selection).toArray();
            for (Object element : elements) {
                if (element instanceof KeYClassPathEntry) {
                    KeYClassPathEntry entry = (KeYClassPathEntry)element;
                    int index = classPathEntries.indexOf(entry);
                    if (index >= 1) {
                        classPathEntries.remove(index);
                        classPathEntries.add(index - 1, entry);
                    }
                }
            }
        }
        updateClassPathViewer();
        classPathTableViewer.setSelection(selection);
    }

    /**
     * Removes the selected class path entries from the viewer.
     */
    public void removeSelectedClassPathEntries() {
        ISelection selection = classPathTableViewer.getSelection();
        if (selection instanceof IStructuredSelection) {
            classPathEntries.removeAll(((IStructuredSelection)selection).toList());
            updateClassPathViewer();
            updateValidState();
        }
    }

    /**
     * Updates the viewer.
     */
    protected void updateClassPathViewer() {
        classPathTableViewer.setInput(classPathEntries);
        handleClassPathViewerSelectionChanged();
    }
    
    /**
     * Handles the event that new elements are selected.
     */
    protected void handleClassPathViewerSelectionChanged() {
        ISelection selection = classPathTableViewer.getSelection();
        removeButton.setEnabled(!selection.isEmpty());
        upButton.setEnabled(!selection.isEmpty());
        downButton.setEnabled(!selection.isEmpty());
    }

    /**
     * Opens the dialog to add external class path entries.
     */
    public void addExternalClassPathEntry() {
        DirectoryDialog dialog = new DirectoryDialog(getShell());
        dialog.setText("Select class path to add");
        dialog.setMessage("Select a directory or create a new one.");
        String directory = dialog.open();
        if (directory != null) {
            KeYClassPathEntry newEntry = new KeYClassPathEntry(KeYClassPathEntryKind.EXTERNAL_IN_FILE_SYSTEM, directory);
            if (!classPathEntries.contains(newEntry)) {
                classPathEntries.add(newEntry);
                updateClassPathViewer();
            }
            selectClassPathEntry(newEntry);
        }
        updateValidState();
    }

    /**
     * Opens the dialog to add external file class path entries.
     */    
    public void addExternalFileClassPathEntry() {
        FileDialog dialog = new FileDialog(getShell(), SWT.MULTI);
        dialog.setText("Select class path file to add");
        dialog.setFilterExtensions(new String[] {"*.*", "*.jar"});
        dialog.setFilterIndex(1);
        dialog.open();
        String[] files = dialog.getFileNames();
        String path = dialog.getFilterPath();
        if (files != null && path != null) {
            for (String file : files) {
                KeYClassPathEntry newEntry = new KeYClassPathEntry(KeYClassPathEntryKind.EXTERNAL_IN_FILE_SYSTEM, path + File.separator + file);
                if (!classPathEntries.contains(newEntry)) {
                    classPathEntries.add(newEntry);
                    updateClassPathViewer();
                }
                selectClassPathEntry(newEntry);
            }
        }
        updateValidState();
    }

    /**
     * Opens the dialog to add workspace class path entries.
     */
    public void addWorkspaceClassPathEntry() {
        IContainer[] result = WorkbenchUtil.openFolderSelection(getShell(), 
                                                                "Select class path to add", 
                                                                "Select a folder, project or create a new one.", 
                                                                true,
                                                                null,
                                                                null);
        if (result != null) {
            List<KeYClassPathEntry> toSelect = new ArrayList<KeYClassPathEntry>(result.length);
            for (IContainer container : result) {
                KeYClassPathEntry newEntry = new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, container.getFullPath().toString());
                toSelect.add(newEntry);
                if (!classPathEntries.contains(newEntry)) {
                    classPathEntries.add(newEntry);
                    updateClassPathViewer();
                }
            }
            selectClassPathEntries(toSelect);
        }
        updateValidState();
    }

    /**
     * Opens the dialog to add workspace file class path entries.
     */    
    public void addWorkspaceFileClassPathEntry() {
        
        IFile[] result = WorkbenchUtil.openFileSelection(getShell(),
                                                         "Select class path file to add",
                                                         "Select a file.", 
                                                         true, 
                                                         null,
                                                         Collections.singleton(new FileExtensionViewerFilter(false, new String[] {"jar", "zip"})));
        if (result != null) {
            List<KeYClassPathEntry> toSelect = new ArrayList<KeYClassPathEntry>(result.length);
            for (IFile file : result) {
                KeYClassPathEntry newEntry = new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, file.getFullPath().toString());
                toSelect.add(newEntry);
                if (!classPathEntries.contains(newEntry)) {
                    classPathEntries.add(newEntry);
                    updateClassPathViewer();
                }
            }
            selectClassPathEntries(toSelect);
        }
        updateValidState();
    }

    /**
     * Selects the given {@link KeYClassPathEntry} instances in the viewer.
     * @param toSelect The {@link KeYClassPathEntry} instances to select.
     */
    protected void selectClassPathEntries(List<KeYClassPathEntry> toSelect) {
        ISelection selection = SWTUtil.createSelection(toSelect);
        classPathTableViewer.setSelection(selection);
    }

    /**
     * Selects the given {@link KeYClassPathEntry} in the viewer.
     * @param toSelect The {@link KeYClassPathEntry} to select.
     */
    protected void selectClassPathEntry(KeYClassPathEntry toSelect) {
       ISelection selection = SWTUtil.createSelection(toSelect);
        classPathTableViewer.setSelection(selection);
    }

    /**
     * Updates the valid state.
     */
    protected void updateValidState() {
        boolean valid = true;
        // Check boot path
        UseBootClassPathKind kind = getUseKind();
        if (UseBootClassPathKind.WORKSPACE.equals(kind)) {
            valid = new KeYClassPathEntry(KeYClassPathEntryKind.WORKSPACE, bootClassPathText.getText()).isValid();
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
            valid = new KeYClassPathEntry(KeYClassPathEntryKind.EXTERNAL_IN_FILE_SYSTEM, bootClassPathText.getText()).isValid();
            if (!valid) {
                if (StringUtil.isEmpty(bootClassPathText.getText())) {
                    setErrorMessage("No external boot class path defined.");
                }
                else {
                    setErrorMessage("The external boot class path \"" + bootClassPathText.getText() + "\" don't exist.");
                }
            }
        }
        // Validate class paths
        if (valid && classPathEntries != null) {
            Iterator<KeYClassPathEntry> iter = classPathEntries.iterator();
            while (valid && iter.hasNext()) {
                KeYClassPathEntry next = iter.next();
                if (!next.isValid()) {
                    valid = false;
                    setErrorMessage("The class path entry \"" + next.getPath() + "\" refers to a not existing " + (KeYClassPathEntryKind.WORKSPACE.equals(next.getKind()) ? "workspace resource" : "external resource") + ".");
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
        addWorkspaceButton.setEnabled(enabled);
        addWorkspaceFileButton.setEnabled(enabled);
        addExternalButton.setEnabled(enabled);
        addExternalFileButton.setEnabled(enabled);
        bootClassPathText.setEditable(enabled && !useDefaultBootClassPathButton.getSelection());
        classPathTableViewer.getTable().setEnabled(enabled);
        useDefaultBootClassPathButton.setEnabled(enabled);
        useWorkspaceBootClassPathButton.setEnabled(enabled);
        useExternalBootClassPathButton.setEnabled(enabled);
        selectBootClassPathButton.setEnabled(enabled && !useDefaultBootClassPathButton.getSelection());
        ISelection selection = classPathTableViewer.getSelection();
        removeButton.setEnabled(enabled && !selection.isEmpty());
        upButton.setEnabled(enabled && !selection.isEmpty());
        downButton.setEnabled(enabled && !selection.isEmpty());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean performOk() {
        try {
            IProject project = getProject();
            KeYResourceProperties.setUseBootClassPathKind(project, getUseKind());
            KeYResourceProperties.setBootClassPath(project, bootClassPathText.getText());
            KeYResourceProperties.setClassPathEntries(project, classPathEntries);
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
        setUseKind(UseBootClassPathKind.KEY_DEFAULT);
        SWTUtil.setText(bootClassPathText, null);
        classPathEntries.clear();
        updateClassPathViewer();
        super.performDefaults();
    }
}