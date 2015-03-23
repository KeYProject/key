package org.key_project.stubby.ui.wizard.page;

import java.util.List;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IJavaProject;
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
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.customization.IStubGenerationCustomization;
import org.key_project.stubby.ui.util.StubbyImages;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.StringUtil;

/**
 * Stub generation {@link WizardPage}.
 * @author Martin Hentschel
 */
public class GenerateStubsWizardPage extends WizardPage {
   /**
    * The {@link IJavaProject} to generate stubs for.
    */
   private final IJavaProject javaProject;
   
   /**
    * The available {@link IStubGenerationCustomization}s.
    */
   private final List<IStubGenerationCustomization> customizations;
   
   /**
    * {@link Text} which defines the stub folder.
    */
   private Text stubFolderText;
   
   /**
    * {@link Button} to select the stub folder.
    */
   private Button selectStubFolderButton;
   
   /**
    * Constructor.
    * @param pageName The page name.
    * @param javaProject The {@link IJavaProject} for which stubs should be generated.
    * @param customizations The available {@link IStubGenerationCustomization}s.
    */
   public GenerateStubsWizardPage(String pageName, IJavaProject javaProject, List<IStubGenerationCustomization> customizations) {
      super(pageName);
      this.javaProject = javaProject;
      this.customizations = customizations;
      setTitle("Generate Stubs");
      setDescription("Define the settings for stub generation.");
      setImageDescriptor(StubbyImages.getImageDescriptor(StubbyImages.GENERATE_STUBS_WIZARD));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(1, false));
      setControl(root);
      // Stub folder group
      Group stubFolderGroup = new Group(root, SWT.NONE);
      stubFolderGroup.setText("Stub Folder");
      stubFolderGroup.setLayout(new GridLayout(2, false));
      stubFolderGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      stubFolderText = new Text(stubFolderGroup, SWT.BORDER);
      stubFolderText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      SWTUtil.setText(stubFolderText, StubGeneratorUtil.getStubFolderPath(javaProject));
      stubFolderText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            handleStubFolderModified(e);
         }
      });
      selectStubFolderButton = new Button(stubFolderGroup, SWT.PUSH);
      selectStubFolderButton.setText("&...");
      selectStubFolderButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            selectStubFolder();
         }
      });
      // Customizations
      if (!CollectionUtil.isEmpty(customizations)) {
         String path = getStubFolderPath();
         for (IStubGenerationCustomization customization : customizations) {
            Control control = customization.createComposite(root);
            if (control != null) {
               control.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
            }
            customization.setStubFolderPath(path);
         }
      }
   }
   
   /**
    * When the stub folder has changed.
    * @param e The {@link ModifyEvent}.
    */
   protected void handleStubFolderModified(ModifyEvent e) {
      String path = getStubFolderPath();
      if (StringUtil.isTrimmedEmpty(path)) {
         setErrorMessage("Stub folder not defined.");
         setPageComplete(false);
      }
      else {
         IResource stubResource = javaProject.getProject().findMember(new Path(path));
         if (stubResource instanceof IFile && stubResource.exists()) {
            setErrorMessage("Stub folder is an existing file.");
            setPageComplete(false);
         }
         else {
            if (!CollectionUtil.isEmpty(customizations)) {
               for (IStubGenerationCustomization customization : customizations) {
                  customization.setStubFolderPath(path);
               }
            }
            setErrorMessage(null);
            setPageComplete(true);
         }
      }
   }

   /**
    * Opens the stub folder selection dialog.
    */
   public void selectStubFolder() {
      IContainer[] result = WorkbenchUtil.openFolderSelection(getShell(),
                                                              "Select stub folder",
                                                              "Select a folder or create a new one.", false,
                                                              new Object[] { javaProject.getProject() }, 
                                                              null,
                                                              javaProject.getProject());
      if (result != null && result.length == 1) {
         String projectPath = result[0].getProject().getFullPath().toString();
         String folderPath = result[0].getFullPath().toString();
         stubFolderText.setText(folderPath.substring(projectPath.length() + 1));
      }
   }
   
   /**
    * Returns the defined stub folder.
    * @return The defined stub folder.
    */
   public String getStubFolderPath() {
      return stubFolderText.getText();
   }
}
