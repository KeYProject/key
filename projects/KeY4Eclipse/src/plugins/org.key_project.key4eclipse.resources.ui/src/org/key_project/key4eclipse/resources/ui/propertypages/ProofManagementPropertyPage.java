package org.key_project.key4eclipse.resources.ui.propertypages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.eclipse.ui.dialogs.PropertyPage;
import org.key_project.key4eclipse.resources.property.KeYProjectProperties;
import org.key_project.key4eclipse.resources.ui.util.LogUtil;

public class ProofManagementPropertyPage extends PropertyPage implements IWorkbenchPropertyPage {

   private Button enableEfficentProofManagementButton;
   
   
   public ProofManagementPropertyPage() {
      // TODO Auto-generated constructor stub
   }

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
      enableEfficentProofManagementButton = new Button(builderSettingsComposite, SWT.CHECK);
      enableEfficentProofManagementButton.setText("Efficient proof management enabled");
      enableDisableButton();
      
      return root;
   }

   
   private void enableDisableButton(){
      IProject project = getProject();
      String enabled;
      try {
         enabled = project.getPersistentProperty(KeYProjectProperties.PROP_ENALBLE_EFFICIENT_PROOFMANAGEMENT);
         if(enabled.equals("TRUE")){
            enableEfficentProofManagementButton.setSelection(true);
         }
         else if(enabled.equals(false)){
            enableEfficentProofManagementButton.setSelection(false);
         }
      }
      catch (CoreException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }
   
   @Override
   public boolean performOk() {
      IProject project = getProject();
      String enabled;
      if(enableEfficentProofManagementButton.getSelection()){
         enabled = "TRUE";
      }
      else {
         enabled = "FALSE";
      }
      try {
         KeYProjectProperties.setEnableEfficientProofManagement(project, enabled);
      }
      catch (CoreException e) {
         LogUtil.getLogger().createErrorStatus(e);
      }
      return super.performOk();
   }
   
   
   @Override
   protected void performDefaults() {
      IProject project = getProject();
      enableEfficentProofManagementButton.setSelection(false);
   try {
      KeYProjectProperties.setEnableEfficientProofManagement(project, "FALSE");
   }
   catch (CoreException e) {
      LogUtil.getLogger().createErrorStatus(e);
   }
      super.performDefaults();
   }
   
   
   
   //TODO: war von martin. nachfragen ob die methode in eine utilklasse kommt oder was sonst damit passiert.
   /**
    * Returns the {@link IProject} that is currently configured.
    * @return The {@link IProject} to configure.
    */
   public IProject getProject() {
       if (getElement() != null) {
           return (IProject)getElement().getAdapter(IProject.class);
       }
       else {
           return null;
       }
   }
}
