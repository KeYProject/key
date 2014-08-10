package org.key_project.key4eclipse.common.ui.completion;

import org.key_project.key4eclipse.common.ui.wizard.CompleteBuiltInRuleAppWizard;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * Provides a basic implementation of {@link InteractiveRuleApplicationCompletion}
 * used in the Eclipse context.
 * @author Martin Hentschel
 */
public abstract class AbstractInteractiveRuleApplicationCompletion implements InteractiveRuleApplicationCompletion {
   /**
    * {@inheritDoc}
    */
   @Override
   public IBuiltInRuleApp complete(IBuiltInRuleApp app, Goal goal, boolean forced) {
      return CompleteBuiltInRuleAppWizard.openWizard(WorkbenchUtil.getActiveShell(), 
                                                     createPerform(app, goal, forced));
   }

   /**
    * Creates the {@link IInteractiveRuleApplicationCompletionPerform} to use.
    * @param app The DefaultBuiltInRuleApp to be completed.
    * @param goal The Goal where the app will later be applied to.
    * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
    * @return The created {@link IInteractiveRuleApplicationCompletionPerform}.
    */
   protected abstract IInteractiveRuleApplicationCompletionPerform createPerform(IBuiltInRuleApp app, Goal goal, boolean forced);
}