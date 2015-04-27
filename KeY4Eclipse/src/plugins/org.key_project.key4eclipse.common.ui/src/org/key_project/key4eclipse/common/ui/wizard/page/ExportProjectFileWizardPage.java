package org.key_project.key4eclipse.common.ui.wizard.page;

import java.io.File;
import java.util.Collections;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.viewers.CheckStateChangedEvent;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.ICheckStateListener;
import org.eclipse.jface.viewers.ICheckStateProvider;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.model.WorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.key_project.key4eclipse.common.ui.util.KeYImages;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.FileExtensionViewerFilter;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;

/**
 * The {@link WizardPage} to define the settings for exporting
 * KeY's project settings into a {@code project.key} file.
 * @author Martin Hentschel
 */
public class ExportProjectFileWizardPage extends WizardPage {
   /**
    * The currently selected {@link IProject}.
    */
   private final IProject selectedProject;
   
   /**
    * Shows the available Java projects.
    */
   private CheckboxTableViewer projectViewer;
   
   /**
    * {@link Button} to define workspace target.
    */
   private Button workspaceButton;
   
   /**
    * {@link Button} to define file system target.
    */
   private Button fileSystemButton;
   
   /**
    * The {@link Text} defining the path.
    */
   private Text locationText;
   
   /**
    * {@link Button} to select a target file.
    */
   private Button selectButton;
   
   /**
    * The currently not shown location (workspace or file system)
    */
   private String otherLocation;

   /**
    * Constructor.
    * @param pageName The name of the {@link WizardPage}.
    * @param selectedProject The currently selected {@link IProject}.
    */
   public ExportProjectFileWizardPage(String pageName, IProject selectedProject) {
      super(pageName);
      this.selectedProject = selectedProject;
      setTitle("Export KeY's project settings as 'project.key' file");
      setMessage("Define the location to save the created file at.");
      setImageDescriptor(KeYImages.getImageDescriptor(KeYImages.KEY_FILE_EXPORT_WIZARD));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(1, false));
      setControl(root);
      // projectsGroup
      Group projectsGroup = new Group(root, SWT.NONE);
      projectsGroup.setText("Project");
      projectsGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
      projectsGroup.setLayout(new GridLayout(1, false));
      projectViewer = CheckboxTableViewer.newCheckList(projectsGroup, SWT.BORDER);
      projectViewer.getTable().setLayoutData(new GridData(GridData.FILL_BOTH));
      projectViewer.setLabelProvider(new WorkbenchLabelProvider());
      projectViewer.setContentProvider(new WorkbenchContentProvider());
      projectViewer.addFilter(new ViewerFilter() {
         @Override
         public boolean select(Viewer viewer, Object parentElement, Object element) {
            if (element instanceof IProject) {
               IProject project = (IProject) element;
               return project.exists() && 
                      project.isOpen() &&
                      JDTUtil.isJavaProject(project);
            }
            else {
               return false;
            }
         }
      });
      projectViewer.setInput(ResourcesPlugin.getWorkspace().getRoot());
      projectViewer.setCheckStateProvider(new ICheckStateProvider() {
         @Override
         public boolean isChecked(Object element) {
            return ObjectUtil.equals(selectedProject, element);
         }
         
         @Override
         public boolean isGrayed(Object element) {
            return false;
         }
      });
      projectViewer.addCheckStateListener(new ICheckStateListener() {
         @Override
         public void checkStateChanged(CheckStateChangedEvent event) {
            handleProjectCheckStateChanged(event);
         }
      });
      // targetGroup
      Group targetGroup = new Group(root, SWT.NONE);
      targetGroup.setText("Target");
      targetGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      targetGroup.setLayout(new GridLayout(1, false));
      // typeComposite
      Composite typeComposite = new Composite(targetGroup, SWT.NONE);
      typeComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      typeComposite.setLayout(new GridLayout(2, false));
      workspaceButton = new Button(typeComposite, SWT.RADIO);
      workspaceButton.setText("&Workspace");
      workspaceButton.setSelection(true);
      workspaceButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleWorkspaceFileSystemChange(e);
         }
      });
      fileSystemButton = new Button(typeComposite, SWT.RADIO);
      fileSystemButton.setText("File &System");
      fileSystemButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            handleWorkspaceFileSystemChange(e);
         }
      });
      // locationComposite
      Composite locationComposite = new Composite(targetGroup, SWT.NONE);
      locationComposite.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      locationComposite.setLayout(new GridLayout(3, false));
      Label locationLabel = new Label(locationComposite, SWT.NONE);
      locationLabel.setText("&Location");
      locationText = new Text(locationComposite, SWT.BORDER);
      locationText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      locationText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageCompleted();
         }
      });
      selectButton = new Button(locationComposite, SWT.PUSH);
      selectButton.setText("&...");
      selectButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            selectLocation();
         }
      });
      updateLocation(selectedProject);
      updatePageCompleted();
   }

   /**
    * Opens the select location dialog.
    */
   protected void selectLocation() {
      if (isWorkspace()) {
         IResource currentFile = ResourcesPlugin.getWorkspace().getRoot().findMember(new Path(getPath()));
         IFile[] result = WorkbenchUtil.openFileSelection(getShell(),
                                                          "Select file to save",
                                                          "Select a file.", 
                                                          false, 
                                                          currentFile != null ? new Object[] {currentFile} : null,
                                                          Collections.singleton(new FileExtensionViewerFilter(false, "key")));
         if (result != null && result.length == 1) {
            SWTUtil.setText(locationText, result[0].getFullPath().toString());
         }
      }
      else {
         FileDialog dialog = new FileDialog(getShell(), SWT.SINGLE);
         dialog.setFileName(getPath());
         dialog.setText("Select file to save");
         dialog.setFilterExtensions(new String[] {"*.*", "*.key"});
         dialog.setFilterIndex(1);
         dialog.open();
         String file = dialog.getFileName();
         if (file != null) {
            SWTUtil.setText(locationText, dialog.getFilterPath() + File.separator + file);
         }
      }
   }

   /**
    * When the type of location has changed.
    * @param e The {@link SelectionEvent}.
    */
   protected void handleWorkspaceFileSystemChange(SelectionEvent e) {
      if (((Button) e.widget).getSelection()) {
         String newOtherLocatin = getPath();
         SWTUtil.setText(locationText, otherLocation);
         otherLocation = newOtherLocatin;         
      }
   }

   /**
    * When a project checked state has changed.
    * @param event The {@link CheckStateChangedEvent}.
    */
   protected void handleProjectCheckStateChanged(CheckStateChangedEvent event) {
      if (!event.getChecked()) {
         // Forbid deselection
         projectViewer.setChecked(event.getElement(), true);
      }
      else {
         IProject newlyCheckedElement = (IProject)event.getElement();
         updatePageCompleted();
         updateLocation(newlyCheckedElement);
         // Ensure that only one element is selected
         Object[] checkedElements = projectViewer.getCheckedElements();
         for (Object element : checkedElements) {
            if (element != event.getElement()) {
               projectViewer.setChecked(element, false);
            }
         }
      }
   }
   
   /**
    * Updates the shown path according to the given {@link IProject}.
    * @param project The {@link IProject}.
    */
   protected void updateLocation(IProject project) {
      if (project != null) {
         IFile file = project.getFile("project.key");
         String projectPath = file.getFullPath().toString();
         String fileSystemPath = ObjectUtil.toString(ResourceUtil.getLocation(file));
         if (isWorkspace()) {
            SWTUtil.setText(locationText, projectPath);
            otherLocation = fileSystemPath;
         }
         else {
            SWTUtil.setText(locationText, fileSystemPath);
            otherLocation = projectPath;
         }
      }
      else {
         SWTUtil.setText(locationText, null);
      }
   }

   /**
    * Updates the page completed state.
    */
   protected void updatePageCompleted() {
      // Validate project
      String errorMessage = null;
      if (ArrayUtil.isEmpty(projectViewer.getCheckedElements())) {
         errorMessage = "No project checked.";
      }
      // Validate location
      if (errorMessage == null && StringUtil.isTrimmedEmpty(getPath())) {
         errorMessage = "No location defined.";
      }
      if (errorMessage == null && isWorkspace()) {
         String path = getPath();
         if (!path.startsWith("/")) {
            errorMessage = "Workspace path has to start with '/'.";
         }
      }
      // Update completed status
      setPageComplete(errorMessage == null);
      setErrorMessage(errorMessage);
   }
   
   /**
    * The checked {@link IProject}.
    * @return The checked {@link IProject} or {@code null} if none is checked.
    */
   public IProject getProject() {
      Object[] elements = projectViewer.getCheckedElements();
      if (!ArrayUtil.isEmpty(elements) && elements[0] instanceof IProject) {
         return (IProject) elements[0];
      }
      else {
         return null;
      }
   }
   
   /**
    * Checks if the target is workspace.
    * @return {@code true} workspace, {@code false} file system.
    */
   public boolean isWorkspace() {
      return workspaceButton.getSelection();
   }
   
   /**
    * Returns the path.
    * @return The path.
    */
   public String getPath() {
      return locationText.getText();
   }
}
