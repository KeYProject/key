package org.key_project.key4eclipse.common.ui.completion;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Shell;
import org.key_project.key4eclipse.common.ui.dialog.ContractSelectionDialog;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.CollectionUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.Contract;
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
       * Constructor.
       * @param app The DefaultBuiltInRuleApp to be completed.
       * @param goal The Goal where the app will later be applied to.
       * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
       */
      public Perform(IBuiltInRuleApp app, Goal goal, boolean forced) {
         super(app, goal, forced);
         Services services = goal.proof().getServices();
         inst = UseOperationContractRule.computeInstantiation(app.posInOccurrence().subTerm(), getServices());
         contracts = UseOperationContractRule.getApplicableContracts(inst, getServices());
         Shell parent = WorkbenchUtil.getActiveShell();
         ImmutableCollectionContentProvider contentProvider = ImmutableCollectionContentProvider.getInstance();
         ContractSelectionDialog dialog = new ContractSelectionDialog(parent, contentProvider, services);
         dialog.setTitle("Select Contract for Proof in KeY");
         dialog.setMessage("Select contract to prove.");
         dialog.setInput(contracts);
         
         if(!contracts.isEmpty()){
            dialog.setInitialSelections(new Contract[] {CollectionUtil.getFirst(contracts)});
         }
         
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
//         Label label = new Label(root, SWT.NONE);
//         label.setText("This functionality will be available soon...");
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
         return null;
      }
   }
}
