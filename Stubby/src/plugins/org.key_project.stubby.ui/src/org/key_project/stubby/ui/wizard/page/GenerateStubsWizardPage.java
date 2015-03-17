package org.key_project.stubby.ui.wizard.page;

import org.eclipse.core.resources.IContainer;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Text;
import org.key_project.stubby.core.util.StubGeneratorUtil;
import org.key_project.stubby.ui.util.StubbyImages;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

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
    */
   public GenerateStubsWizardPage(String pageName, IJavaProject javaProject) {
      super(pageName);
      this.javaProject = javaProject;
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
      Group stubFolderGroup = new Group(root, SWT.NONE);
      stubFolderGroup.setText("Stub Folder");
      stubFolderGroup.setLayout(new GridLayout(2, false));
      stubFolderGroup.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      stubFolderText = new Text(stubFolderGroup, SWT.BORDER);
      stubFolderText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      SWTUtil.setText(stubFolderText, StubGeneratorUtil.getStubFolderPath(javaProject));
      selectStubFolderButton = new Button(stubFolderGroup, SWT.PUSH);
      selectStubFolderButton.setText("&...");
      selectStubFolderButton.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            selectStubFolder();
         }
      });
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
