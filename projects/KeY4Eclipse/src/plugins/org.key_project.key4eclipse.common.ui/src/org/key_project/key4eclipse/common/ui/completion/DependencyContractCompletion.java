package org.key_project.key4eclipse.common.ui.completion;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import javax.swing.JComboBox;
import javax.swing.JOptionPane;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ListViewer;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.gui.DependencyContractCompletion.TermStringWrapper;
import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;

/**
 * The {@link InteractiveRuleApplicationCompletion} to treat {@link UseDependencyContractRule} in the Eclipse context.
 * @author Martin Hentschel
 */
public class DependencyContractCompletion extends AbstractInteractiveRuleApplicationCompletion {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canComplete(IBuiltInRuleApp app) {
      return de.uka.ilkd.key.gui.DependencyContractCompletion.checkCanComplete(app);
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
       * The {@link UseDependencyContractApp}.
       */
      private UseDependencyContractApp cApp;
      
      /**
       * The used {@link Services}.
       */
      private final Services services;
      
      private final List<PosInOccurrence> steps;
      
      private final TermStringWrapper[] heaps;
      
      private Object[] selectedHeap;
      
      /**
       * Constructor.
       * @param app The DefaultBuiltInRuleApp to be completed.
       * @param goal The Goal where the app will later be applied to.
       * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
       */
      public Perform(IBuiltInRuleApp app, Goal goal, boolean forced) {
         super(app, goal, forced);
         cApp = (UseDependencyContractApp) app;

         services = goal.proof().getServices();

         cApp = cApp.tryToInstantiateContract(services);
         
         steps = UseDependencyContractRule.getSteps(app.getHeapContext(), cApp.posInOccurrence(), goal.sequent(), services);
                  
         assert app.getHeapContext() != null;

         if (steps.size() >= 1) {
            // prepare array of possible base heaps
            heaps = new TermStringWrapper[steps.size()];
            final LogicPrinter lp = new LogicPrinter(null, new NotationInfo(), services);
            lp.setLineWidth(120);

            de.uka.ilkd.key.gui.DependencyContractCompletion.extractHeaps(app.getHeapContext(), steps, heaps, lp); 
         }
         else {
            heaps = new TermStringWrapper[0];
         }
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getWindowTitle() {
         return "Instantiation";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getTitle() {
         return "Instantiation";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getDescription() {
         return "Please select base heap configuration:";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createControl(Composite root) {
         ListViewer viewer = new ListViewer(root, SWT.BORDER | SWT.SINGLE);         
         ArrayContentProvider provider = new ArrayContentProvider();
         viewer.setContentProvider(provider);
         viewer.setInput(heaps);
         viewer.addSelectionChangedListener(new ISelectionChangedListener() {
            
            @Override
            public void selectionChanged(SelectionChangedEvent event) {
               ISelection selection = event.getSelection();
               selectedHeap = SWTUtil.toArray(selection);
            }
         });
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
         final Term[] resultHeaps = null; // TODO: Assign selected heap.
         
         
         
         PosInOccurrence step = de.uka.ilkd.key.gui.DependencyContractCompletion.findCorrespondingStep(steps, resultHeaps);
         if (step == null) {
            return null;
        }
        return cApp.setStep(step);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
      }
   }
}
