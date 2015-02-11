package org.key_project.key4eclipse.common.ui.completion;

import java.util.List;

import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.TableViewerColumn;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.key_project.key4eclipse.common.ui.provider.ContractLabelProvider;
import org.key_project.key4eclipse.common.ui.provider.ImmutableCollectionContentProvider;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.BlockContractSelectionPanel;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.BlockContractRule.Instantiation;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.HeapContext;

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
       * The used {@link Services}.
       */
      private final Services services;
      
      /**
       * The {@link TableViewer} which shows the contracts
       */
      private TableViewer viewer;
      
      /**
       * The {@link ContractLabelProvider} used in {@link #viewer}
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
         TableColumnLayout tableLayout = new TableColumnLayout(); // The TableColumnLayout together with the not visible TableViewerColumn ensure that no vertical column lines are shown.
         Composite viewerComposite = new Composite(root, SWT.NONE);
         viewerComposite.setLayout(tableLayout);
         viewer = new TableViewer(viewerComposite);
         viewer.getTable().setLinesVisible(true);
         TableViewerColumn contractColumn = new TableViewerColumn(viewer, SWT.NONE);
         contractColumn.getColumn().setText("Kind");
         tableLayout.setColumnData(contractColumn.getColumn(), new ColumnWeightData(100));
         viewer.setContentProvider(ImmutableCollectionContentProvider.getInstance());
         labelViewer = new ContractLabelProvider(services);
         viewer.setLabelProvider(labelViewer);
         viewer.setInput(contracts);
         viewer.addSelectionChangedListener(new ISelectionChangedListener() {
             @Override
             public void selectionChanged(SelectionChangedEvent event) {
                updateErrorMessage();
             }
         });
         updateErrorMessage();
      }
      
      /**
       * 
       */
      protected void updateErrorMessage() {
         ISelection selection = viewer.getSelection();
         if(!selection.isEmpty()) {
            setErrorMessage(null);
         } else {
            setErrorMessage("Please select at least one contract.");
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
         BlockContract contract = getSelectedContract();
         if(contract != null) {
            BlockContractBuiltInRuleApp result = (BlockContractBuiltInRuleApp) getApp();
            final List<LocationVariable> heaps = HeapContext.getModHeaps(services, instantiation.isTransactional());
            result.update(instantiation.block, contract, heaps);
            return result;
         } else {
            return getApp();
         }
      }
      
      /**
       * Returns the selected {@link Contract}.
       * @return The selected {@link Contract} or {@code null} if not available.
       */
      protected BlockContract getSelectedContract() {
         final Object[] selection = SWTUtil.toArray(viewer.getSelection());
         return BlockContractSelectionPanel.computeContract(services, selection);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
      }
   }
}
