package org.key_project.sed.ui.visualization.execution_tree.wizard.page;

import java.util.List;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.execution_tree.wizard.CreateDebugNodeWizard;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;

/**
 * {@link WizardPage} to define the initial values of new {@link ISEDDebugNode}s.
 * @author Martin Hentschel
 * @see CreateDebugNodeWizard
 */
public class CreateDebugNodeWizardPage extends WizardPage {
   /**
    * The existing business objects.
    */
   private List<ISEDDebugNode> businessObjects;
   
   /**
    * Input field for the name.
    */
   private Text nameText;
   
   /**
    * Input field to define the parent.
    */
   private Combo parentCombo;
   
   /**
    * Constructor.
    * @param pageName The page name.
    * @param nodeType The name of the node type which should be created.
    * @param businessObjects The existing business objects.
    */
   public CreateDebugNodeWizardPage(String pageName, String nodeType, List<ISEDDebugNode> businessObjects) {
      super(pageName);
      this.businessObjects = businessObjects;
      setTitle("Create " + nodeType);
      setDescription("Define the properties for the new " + nodeType + ".");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Create root
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(2, false));
      setControl(root);
      // Create name 
      Label nameLabel = new Label(root, SWT.NONE);
      nameLabel.setText("&Name");
      nameText = new Text(root, SWT.BORDER);
      nameText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      nameText.addModifyListener(new ModifyListener() {
         @Override
         public void modifyText(ModifyEvent e) {
            updatePageCompleted();
         }
      });
      // Parent combo
      if (isParentRequired()) {
         Label parentLabel = new Label(root, SWT.NONE);
         parentLabel.setText("&Parent");
         parentCombo = new Combo(root, SWT.READ_ONLY);
         parentCombo.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         parentCombo.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               updatePageCompleted();
            }
         });
         for (ISEDDebugNode node : businessObjects) {
            SWTUtil.add(parentCombo, ObjectUtil.toString(node));
         }
      }
      // Update page completed
      updatePageCompleted();
   }
   
   /**
    * Updates the page completed status.
    */
   protected void updatePageCompleted() {
      // Compute page completed status
      boolean valid = !StringUtil.isTrimmedEmpty(getNameValue());
      if (!valid) {
         setErrorMessage("No name defined.");
      }
      if (valid && isParentRequired()) {
         ISEDDebugNode parent = getParent();
         valid = parent != null;
         if (!valid) {
            setErrorMessage("No parent selected.");
         }
      }
      // Update page completed status
      setPageComplete(valid);
      if (valid) {
         setErrorMessage(null);
      }
   }

   /**
    * Returns the defined name.
    * @return The defined name.
    */
   public String getNameValue() {
      return nameText.getText();
   }
   
   /**
    * Checks if a parent is required.
    * @return {@code true} parent is required, {@code false} parent is not required.
    */
   public boolean isParentRequired() {
      return businessObjects != null;
   }
   
   /**
    * Returns the selected parent {@link ISEDDebugNode}.
    * @return The parent {@link ISEDDebugNode}.
    */
   public ISEDDebugNode getParent() {
      int index = parentCombo.getSelectionIndex();
      if (index >= 0 && index < businessObjects.size()) {
         return businessObjects.get(index);
      }
      else {
         return null;
      }
   }
}
