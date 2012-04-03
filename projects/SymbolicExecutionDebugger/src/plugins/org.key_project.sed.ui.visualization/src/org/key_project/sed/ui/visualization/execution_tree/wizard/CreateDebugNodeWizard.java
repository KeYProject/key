package org.key_project.sed.ui.visualization.execution_tree.wizard;

import java.util.List;

import org.eclipse.jface.wizard.Wizard;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Shell;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.execution_tree.wizard.page.CreateDebugNodeWizardPage;

/**
 * {@link Wizard} to define the initial values of new {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 * @see CreateDebugNodeWizardPage
 */
public class CreateDebugNodeWizard extends Wizard {
   /**
    * The contained {@link CreateDebugNodeWizardPage}.
    */
   private CreateDebugNodeWizardPage propertyPage;
   
   /**
    * The name of the node type which should be created.
    */
   private String nodeType;

   /**
    * The existing business objects.
    */
   private List<ISEDDebugNode> businessObjects;
   
   /**
    * The result of this {@link Wizard}.
    */
   private CreateDebugNodeWizardResult result;
   
   /**
    * Constructor.
    * @param nodeType The name of the node type which should be created.
    * @param businessObjects The existing business objects.
    */
   public CreateDebugNodeWizard(String nodeType, List<ISEDDebugNode> businessObjects) {
      super();
      this.nodeType = nodeType;
      this.businessObjects = businessObjects;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPages() {
      setWindowTitle("Create " + nodeType);
      propertyPage = new CreateDebugNodeWizardPage("propertyPage", nodeType, businessObjects);
      addPage(propertyPage);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean performFinish() {
      result = new CreateDebugNodeWizardResult(propertyPage.getNameValue(),
                                               propertyPage.isParentRequired() ? propertyPage.getParent() : null);
      return true;
   }
   
   /**
    * Returns the wizard result.
    * @return The wizard result or {@code null} if the wizard was canceled.
    */
   public CreateDebugNodeWizardResult getResult() {
      return result;
   }

   /**
    * Opens the this {@link Wizard} in an {@link WizardDialog}.
    * @param parentShell The parent {@link Shell} to use.
    * @param nodeType The name of the node type which should be created.
    * @param businessObjects The existing business objects.
    * @return The wizard result or {@code null} if the wizard was canceled.
    */
   public static CreateDebugNodeWizardResult openWizard(Shell parentShell, 
                                                        String nodeType,
                                                        List<ISEDDebugNode> businessObjects) {
      CreateDebugNodeWizard wizard = new CreateDebugNodeWizard(nodeType, businessObjects);
      WizardDialog dialog = new WizardDialog(parentShell, wizard);
      dialog.setHelpAvailable(false);
      if (dialog.open() == WizardDialog.OK) {
         return wizard.getResult();
      }
      else {
         return null;
      }
   }
   
   /**
    * The wizard result with the defined settings.
    * @author Martin Hentschel
    */
   public static class CreateDebugNodeWizardResult {
      /**
       * The name of the {@link ISEDDebugNode} to create.
       */
      private String name;

      /**
       * The selected parent {@link ISEDDebugNode} or {@code null} if no parent is required.
       */
      private ISEDDebugNode parent;
      
      /**
       * Constructor.
       * @param name The name of the {@link ISEDDebugNode} to create.
       * @param parent The selected parent {@link ISEDDebugNode} or {@code null} if no parent is required.
       */
      public CreateDebugNodeWizardResult(String name, ISEDDebugNode parent) {
         super();
         this.name = name;
         this.parent = parent;
      }

      /**
       * Returns the name of the {@link ISEDDebugNode} to create.
       * @return The name of the {@link ISEDDebugNode} to create.
       */
      public String getName() {
         return name;
      }

      /**
       * Returns the selected parent {@link ISEDDebugNode} or {@code null} if no parent is required.
       * @return The selected parent {@link ISEDDebugNode} or {@code null} if no parent is required.
       */
      public ISEDDebugNode getParent() {
         return parent;
      }
   }
}
