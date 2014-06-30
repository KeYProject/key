package org.key_project.key4eclipse.common.ui.completion;

import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.widgets.Composite;
import org.key_project.key4eclipse.common.ui.provider.ContractLabelProvider;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

/**
 * The {@link InteractiveRuleApplicationCompletion} to treat {@link UseOperationContractRule} in the Eclipse context.
 * @author Martin Hentschel
 */
public class FunctionalOperationContractCompletion extends AbstractInteractiveRuleApplicationCompletion {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canComplete(IBuiltInRuleApp app) {
      return de.uka.ilkd.key.gui.FunctionalOperationContractCompletion.checkCanComplete(app);
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
      private final Instantiation inst;
      
      /**
       * The {@link FunctionalOperationContract}s
       */
      private final ImmutableSet<FunctionalOperationContract> contracts;
      
      /**
       * The used {@link Services}.
       */
      private final Services services;
      
      /**
       * The {@link TableViewer} which shows the contracts.
       */
      private TableViewer viewer;
      
      /**
       * The {@link ContractLabelProvider} used in {@link #viewer}.
       */
      private ContractLabelProvider labelViewer;
      
      /**
       * Constructor.
       * @param app The DefaultBuiltInRuleApp to be completed.
       * @param goal The Goal where the app will later be applied to.
       * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
       */
      public Perform(IBuiltInRuleApp app, Goal goal, boolean forced) {
         super(app, goal, forced);
         services = goal.proof().getServices();
         inst = UseOperationContractRule.computeInstantiation(app.posInOccurrence().subTerm(), getServices());
         contracts = UseOperationContractRule.getApplicableContracts(inst, getServices());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getWindowTitle() {
         return "Contracts for " + inst.pm.getName();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getTitle() {
         return "Contracts for " + inst.pm.getName();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createControl(Composite root) {
         viewer = new TableViewer(root);
         viewer.setContentProvider(ImmutableCollectionContentProvider.getInstance());
         labelViewer = new ContractLabelProvider(services);
         viewer.setLabelProvider(labelViewer);
         viewer.setInput(contracts);
         // TODO: Ensure that "Finish" is only available when at least one contract is selected (use setErrorMessage)
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
         return null; // TODO: Implement similar as de.uka.ilkd.key.collection.ImmutableSet.FunctionalOperationContractCompletion
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
         if (labelViewer != null) {
            labelViewer.dispose();
         }
      }
   }
}
