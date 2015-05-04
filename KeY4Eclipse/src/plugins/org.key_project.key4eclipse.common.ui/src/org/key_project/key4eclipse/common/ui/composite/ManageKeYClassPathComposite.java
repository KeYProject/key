package org.key_project.key4eclipse.common.ui.composite;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.DirectoryDialog;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.key_project.key4eclipse.common.ui.property.KeYProjectPropertyPage;
import org.key_project.key4eclipse.common.ui.provider.KeYClassPathEntryLabelProvider;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry;
import org.key_project.key4eclipse.starter.core.property.KeYPathEntry.KeYPathEntryKind;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.BeanComposite;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.FileExtensionViewerFilter;

public class ManageKeYClassPathComposite extends BeanComposite {
   /**
    * Property {@link #getClassPathEntries()}.
    */
   public static final String PROP_CLASS_PATH_ENTRIES = "classPathEntries";

   /**
    * The supported file extensions.
    */
   private final String[] supportedFileExtensions;
   
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
    * Contains the shown class path entries.
    */
   private List<KeYPathEntry> classPathEntries = new LinkedList<KeYPathEntry>();

   public ManageKeYClassPathComposite(Composite parent, int style, String title, boolean supportsDirectories, boolean supportsUpAndDown, String... supportedFileExtensions) {
      super(parent, style);
      this.supportedFileExtensions = supportedFileExtensions;
      setLayout(KeYProjectPropertyPage.createGridLayout(1, false));
      Group classPathGroup = new Group(this, SWT.NONE);
      classPathGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      classPathGroup.setLayout(new GridLayout(2, false));
      classPathGroup.setText(title);
      Composite classPathComposite = new Composite(classPathGroup, SWT.NONE);
      classPathComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      classPathComposite.setLayout(KeYProjectPropertyPage.createGridLayout(2, false));
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
      classPathButtonComposite.setLayout(KeYProjectPropertyPage.createGridLayout(1, true));
      if (supportsDirectories) {
         addWorkspaceButton = new Button(classPathButtonComposite, SWT.PUSH);
         addWorkspaceButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         addWorkspaceButton.setText("Add Works&pace");
         addWorkspaceButton.addSelectionListener(new SelectionAdapter() {
             @Override
             public void widgetSelected(SelectionEvent e) {
                 addWorkspaceClassPathEntry();
             }
         });
      }
      addWorkspaceFileButton = new Button(classPathButtonComposite, SWT.PUSH);
      addWorkspaceFileButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      addWorkspaceFileButton.setText("Add Workspace F&ile");
      addWorkspaceFileButton.addSelectionListener(new SelectionAdapter() {
          @Override
          public void widgetSelected(SelectionEvent e) {
              addWorkspaceFileClassPathEntry();
          }
      });
      if (supportsDirectories) {
         addExternalButton = new Button(classPathButtonComposite, SWT.PUSH);
         addExternalButton.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         addExternalButton.setText("Add Externa&l");
         addExternalButton.addSelectionListener(new SelectionAdapter() {
             @Override
             public void widgetSelected(SelectionEvent e) {
                 addExternalClassPathEntry();
             }
         });
      }
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
      if (supportsUpAndDown) {
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
      }
   }

   /**
    * Moves the selected entries one up if possible.
    */
   public void moveSelectedClassPathEntriesDown() {
       List<KeYPathEntry> newEntries = new LinkedList<KeYPathEntry>(classPathEntries);
       ISelection selection = classPathTableViewer.getSelection();
       if (selection instanceof IStructuredSelection) {
           Object[] elements = ((IStructuredSelection)selection).toArray();
           for (int i = elements.length - 1; i >= 0; i--) {
               if (elements[i] instanceof KeYPathEntry) {
                   KeYPathEntry entry = (KeYPathEntry)elements[i];
                   int index = newEntries.indexOf(entry);
                   if (index < newEntries.size() - 1) {
                       newEntries.remove(index);
                       newEntries.add(index + 1, entry);
                   }
               }
           }
       }
       setClassPathEntries(newEntries);
       classPathTableViewer.setSelection(selection);
   }

   /**
    * Moves the selected entries one down if possible.
    */
   public void moveSelectedClassPathEntriesUp() {
       List<KeYPathEntry> newEntries = new LinkedList<KeYPathEntry>(classPathEntries);
       ISelection selection = classPathTableViewer.getSelection();
       if (selection instanceof IStructuredSelection) {
           Object[] elements = ((IStructuredSelection)selection).toArray();
           for (Object element : elements) {
               if (element instanceof KeYPathEntry) {
                   KeYPathEntry entry = (KeYPathEntry)element;
                   int index = newEntries.indexOf(entry);
                   if (index >= 1) {
                      newEntries.remove(index);
                      newEntries.add(index - 1, entry);
                   }
               }
           }
       }
       setClassPathEntries(newEntries);
       classPathTableViewer.setSelection(selection);
   }

   /**
    * Removes the selected class path entries from the viewer.
    */
   public void removeSelectedClassPathEntries() {
       ISelection selection = classPathTableViewer.getSelection();
       if (selection instanceof IStructuredSelection) {
           List<KeYPathEntry> newEntries = new LinkedList<KeYPathEntry>(classPathEntries);
           newEntries.removeAll(((IStructuredSelection)selection).toList());
           setClassPathEntries(newEntries);
       }
   }
   
   /**
    * Handles the event that new elements are selected.
    */
   protected void handleClassPathViewerSelectionChanged() {
       ISelection selection = classPathTableViewer.getSelection();
       removeButton.setEnabled(!selection.isEmpty());
       if (upButton != null) {
          upButton.setEnabled(!selection.isEmpty());
       }
       if (downButton != null) {
          downButton.setEnabled(!selection.isEmpty());
       }
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
           KeYPathEntry newEntry = new KeYPathEntry(KeYPathEntryKind.EXTERNAL_IN_FILE_SYSTEM, directory);
           if (!classPathEntries.contains(newEntry)) {
               List<KeYPathEntry> newEntries = new LinkedList<KeYPathEntry>(classPathEntries);
               newEntries.add(newEntry);
               setClassPathEntries(newEntries);
           }
           selectClassPathEntry(newEntry);
       }
   }

   /**
    * Opens the dialog to add external file class path entries.
    */    
   public void addExternalFileClassPathEntry() {
       FileDialog dialog = new FileDialog(getShell(), SWT.MULTI);
       dialog.setText("Select class path file to add");
       String[] extensions = new String[supportedFileExtensions.length + 1];
       extensions[0] = "*.*";
       for (int i = 0; i < supportedFileExtensions.length; i++) {
          extensions[i + 1] = "*." + supportedFileExtensions[i];
       }
       dialog.setFilterExtensions(extensions);
       dialog.setFilterIndex(1);
       dialog.open();
       String[] files = dialog.getFileNames();
       String path = dialog.getFilterPath();
       if (files != null && path != null) {
           for (String file : files) {
               KeYPathEntry newEntry = new KeYPathEntry(KeYPathEntryKind.EXTERNAL_IN_FILE_SYSTEM, path + File.separator + file);
               if (!classPathEntries.contains(newEntry)) {
                   List<KeYPathEntry> newEntries = new LinkedList<KeYPathEntry>(classPathEntries);
                   newEntries.add(newEntry);
                   setClassPathEntries(newEntries);
               }
               selectClassPathEntry(newEntry);
           }
       }
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
           List<KeYPathEntry> toSelect = new ArrayList<KeYPathEntry>(result.length);
           for (IContainer container : result) {
               KeYPathEntry newEntry = new KeYPathEntry(KeYPathEntryKind.WORKSPACE, container.getFullPath().toString());
               toSelect.add(newEntry);
               if (!classPathEntries.contains(newEntry)) {
                   List<KeYPathEntry> newEntries = new LinkedList<KeYPathEntry>(classPathEntries);
                   newEntries.add(newEntry);
                   setClassPathEntries(newEntries);
               }
           }
           selectClassPathEntries(toSelect);
       }
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
                                                        Collections.singleton(new FileExtensionViewerFilter(false, supportedFileExtensions)));
       if (result != null) {
           List<KeYPathEntry> toSelect = new ArrayList<KeYPathEntry>(result.length);
           for (IFile file : result) {
               KeYPathEntry newEntry = new KeYPathEntry(KeYPathEntryKind.WORKSPACE, file.getFullPath().toString());
               toSelect.add(newEntry);
               if (!classPathEntries.contains(newEntry)) {
                   List<KeYPathEntry> newEntries = new LinkedList<KeYPathEntry>(classPathEntries);
                   newEntries.add(newEntry);
                   setClassPathEntries(newEntries);
               }
           }
           selectClassPathEntries(toSelect);
       }
       setClassPathEntries(classPathEntries);
   }

   /**
    * Selects the given {@link KeYPathEntry} instances in the viewer.
    * @param toSelect The {@link KeYPathEntry} instances to select.
    */
   protected void selectClassPathEntries(List<KeYPathEntry> toSelect) {
       ISelection selection = SWTUtil.createSelection(toSelect);
       classPathTableViewer.setSelection(selection);
   }

   /**
    * Selects the given {@link KeYPathEntry} in the viewer.
    * @param toSelect The {@link KeYPathEntry} to select.
    */
   protected void selectClassPathEntry(KeYPathEntry toSelect) {
      ISelection selection = SWTUtil.createSelection(toSelect);
      classPathTableViewer.setSelection(selection);
   }
   
   /**
    * Enables or disables all UI controls.
    * @param enabled The enabled state to set.
    */
   public void setEnabled(boolean enabled) {
       if (addWorkspaceButton != null) {
          addWorkspaceButton.setEnabled(enabled);
       }
       addWorkspaceFileButton.setEnabled(enabled);
       if (addExternalButton != null) {
          addExternalButton.setEnabled(enabled);
       }
       addExternalFileButton.setEnabled(enabled);
       classPathTableViewer.getTable().setEnabled(enabled);
       ISelection selection = classPathTableViewer.getSelection();
       removeButton.setEnabled(enabled && !selection.isEmpty());
       if (upButton != null) {
          upButton.setEnabled(enabled && !selection.isEmpty());
       }
       if (downButton != null) {
          downButton.setEnabled(enabled && !selection.isEmpty());
       }
   }

   public List<KeYPathEntry> getClassPathEntries() {
      return classPathEntries;
   }

   public void setClassPathEntries(List<KeYPathEntry> classPathEntries) {
      if (classPathEntries == null) {
         classPathEntries = new LinkedList<KeYPathEntry>();
      }
      List<KeYPathEntry> oldValue = getClassPathEntries();
      this.classPathEntries = classPathEntries;
      classPathTableViewer.setInput(classPathEntries);
      handleClassPathViewerSelectionChanged();
      firePropertyChange(PROP_CLASS_PATH_ENTRIES, oldValue, getClassPathEntries());
   }
}
