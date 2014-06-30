package org.key_project.key4eclipse.common.ui.completion;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.BlockContractRule.Instantiation;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;

/**
 * The {@link InteractiveRuleApplicationCompletion} to treat {@link BlockContractRule} in the Eclipse context.
 * @author Martin Hentschel
 */
public class BlockContractCompletion extends AbstractInteractiveRuleApplicationCompletion {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canComplete(IBuiltInRuleApp app) {
      return de.uka.ilkd.key.gui.BlockContractCompletion.checkCanComplete(app);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IInteractiveRuleApplicationCompletionPerform createPerform(IBuiltInRuleApp app, Goal goal, boolean forced) {
      return new Perform(app, goal, forced);
   }
   
   /**
    * The used {@link IInteractiveRuleApplicationCompletionPerform}.
    * @author Martin Hentschel
    */
   public static class Perform extends AbstractInteractiveRuleApplicationCompletionPerform {
      /**
       * The {@link Instantiation}.
       */
      private final Instantiation instantiation;
      
      /**
       * The {@link BlockContract}s.
       */
      private final ImmutableSet<BlockContract> contracts;
      
      /**
       * Constructor.
       * @param app The DefaultBuiltInRuleApp to be completed.
       * @param goal The Goal where the app will later be applied to.
       * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
       */
      public Perform(IBuiltInRuleApp app, Goal goal, boolean forced) {
         super(app, goal, forced);
         setErrorMessage("Functionality is not available yet.");
         instantiation = BlockContractRule.instantiate(app.posInOccurrence().subTerm(), goal, getServices());
         contracts = BlockContractRule.getApplicableContracts(instantiation, goal, getServices());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getWindowTitle() {
         return "Contracts for Block: " + instantiation.block;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getTitle() {
         return "Contracts for Block: " + instantiation.block;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createControl(Composite root) {
         Label label = new Label(root, SWT.NONE);
         label.setText("This functionality will be available soon...");
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
      }
   }
}
