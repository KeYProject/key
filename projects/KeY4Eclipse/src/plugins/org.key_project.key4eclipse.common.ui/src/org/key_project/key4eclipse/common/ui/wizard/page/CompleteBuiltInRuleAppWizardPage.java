package org.key_project.key4eclipse.common.ui.wizard.page;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.key_project.key4eclipse.common.ui.completion.IInteractiveRuleApplicationCompletionPerform;
import org.key_project.key4eclipse.common.ui.wizard.CompleteBuiltInRuleAppWizard;

/**
 * The only {@link WizardPage} shown in a {@link CompleteBuiltInRuleAppWizard}.
 * @author Martin Hentschel
 */
public class CompleteBuiltInRuleAppWizardPage extends WizardPage {
   /**
    * The {@link IInteractiveRuleApplicationCompletionPerform} to use.
    */
   private final IInteractiveRuleApplicationCompletionPerform perform;
   
   /**
    * Listens for {@link IInteractiveRuleApplicationCompletionPerform#getErrorMessage()} changes on {@link #perform}.
    */
   private final PropertyChangeListener performListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         handlePropertyChange(evt);
      }
   };
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param perform The {@link IInteractiveRuleApplicationCompletionPerform} to use. 
    */
   public CompleteBuiltInRuleAppWizardPage(String pageName, IInteractiveRuleApplicationCompletionPerform perform) {
      super(pageName);
      Assert.isNotNull(perform);
      this.perform = perform;
      this.perform.addPropertyChangeListener(IInteractiveRuleApplicationCompletionPerform.PROP_ERROR_MESSAGE, performListener);
      setTitle(perform.getTitle());
      setDescription(perform.getDescription());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      perform.removePropertyChangeListener(IInteractiveRuleApplicationCompletionPerform.PROP_ERROR_MESSAGE, performListener);
      perform.dispose();
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Create root
      Composite root = new Composite(parent, SWT.NONE);
      root.setLayout(new FillLayout());
      setControl(root);
      // Create content
      perform.createControl(root);
      // Set initial page complete state.
      updatePageComplete();
   }

   /**
    * When {@link IInteractiveRuleApplicationCompletionPerform#getErrorMessage()} on {@link #perform} has changed.
    * @param evt The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent evt) {
      updatePageComplete();
   }
   
   /**
    * Checks the user input for validity and updates the page complete state.
    */
   protected void updatePageComplete() {
      String errorMessgae = perform.getErrorMessage();
      setPageComplete(errorMessgae == null);
      setErrorMessage(errorMessgae);
   }
}
