package org.key_project.key4eclipse.common.ui.completion;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.services.IDisposable;
import org.key_project.key4eclipse.common.ui.wizard.CompleteBuiltInRuleAppWizard;
import org.key_project.key4eclipse.common.ui.wizard.page.CompleteBuiltInRuleAppWizardPage;
import org.key_project.util.bean.IBean;

import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * Defines the content and the behavior of the {@link CompleteBuiltInRuleAppWizard}
 * and its {@link CompleteBuiltInRuleAppWizardPage}.
 * @author Martin Hentschel
 */
public interface IInteractiveRuleApplicationCompletionPerform extends IBean, IDisposable {
   /**
    * Property {@link #getTitle()}.
    */
   public static final String PROP_ERROR_MESSAGE = "errorMessage";

   /**
    * Returns the shown window title.
    * @return The shown window title.
    */
   public String getWindowTitle();

   /**
    * Returns the title of the {@link WizardPage}.
    * @return The title of the {@link WizardPage}.
    */
   public String getTitle();

   /**
    * Returns the description of the {@link WizardPage}.
    * @return The description of the {@link WizardPage}.
    */
   public String getDescription();

   /**
    * Creates the content to show in the {@link WizardPage}.
    * @param root The parent {@link Composite}.
    */
   public void createControl(Composite root);

   /**
    * Returns the current error message.
    * @return The current error message or {@code null} if everything is valid.
    */
   public String getErrorMessage();

   /**
    * Performs the finish.
    * @return The resulting {@link IBuiltInRuleApp}.
    */
   public IBuiltInRuleApp finish();
}
