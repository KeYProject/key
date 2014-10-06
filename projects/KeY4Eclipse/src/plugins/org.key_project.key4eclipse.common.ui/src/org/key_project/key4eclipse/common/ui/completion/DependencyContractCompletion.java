package org.key_project.key4eclipse.common.ui.completion;

import java.io.IOException;
import java.util.List;

import javax.swing.JOptionPane;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.DependencyContractCompletion.TermStringWrapper;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;

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
      
      /**
       * The used {@link PosInOccurrence}.
       */
      private PosInOccurrence step;
      
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
         
         final List<PosInOccurrence> steps = UseDependencyContractRule.getSteps(
               app.getHeapContext(),
                   cApp.posInOccurrence(), goal.sequent(), services);
           step = letUserChooseStep(app.getHeapContext(), steps, forced, services);
      }

      /**
       * collects all possible heaps and presents them to the user for selection.
       * If forced is true the user will not be asked if only one alternative is possible
       * @param steps 
       * @param forced
       * @param services
       * @return
       */
      private static PosInOccurrence letUserChooseStep(
           List<LocationVariable> heapContext,
              List<PosInOccurrence> steps, boolean forced, Services services) {
          assert heapContext != null;

          if (steps.size() == 0) {
              return null;
          }

          // prepare array of possible base heaps
          final TermStringWrapper[] heaps = new TermStringWrapper[steps.size()];
          final LogicPrinter lp = new LogicPrinter(null, new NotationInfo(),
                  services);
          lp.setLineWidth(120);

          extractHeaps(heapContext, steps, heaps, lp);

          final Term[] resultHeaps;
          if (!forced) {
              // open dialog
              final TermStringWrapper heapWrapper = (TermStringWrapper) JOptionPane
                      .showInputDialog(MainWindow.getInstance(),
                              "Please select base heap configuration:", "Instantiation",
                              JOptionPane.QUESTION_MESSAGE, null, heaps,
                              heaps.length > 0 ? heaps[0] : null);

              if (heapWrapper == null) {
                  return null;
              }
              resultHeaps = heapWrapper.terms;
          } else {
              resultHeaps = heaps[0].terms;
          }

          // find corresponding step
          for (PosInOccurrence step : steps) {
              boolean match = true;
              for(int j = 0; j<resultHeaps.length; j++) {
                 if (!step.subTerm().sub(j).equals(resultHeaps[j])) {
                    match = false;
                    break;
                 }
              }
              if(match) {
                  return step;
               }
          }

          assert false;
          return null;
      }
      
      private static void extractHeaps(List<LocationVariable> heapContext,
            List<PosInOccurrence> steps, final TermStringWrapper[] heaps,
            final LogicPrinter lp) {
        int i = 0;
        for (PosInOccurrence step : steps) {
            Operator op = step.subTerm().op();
            // necessary distinction (see bug #1232)
            // subterm may either be an observer or a heap term already
            int size = (op instanceof IObserverFunction)?
                ((IObserverFunction)op).getStateCount()*heapContext.size(): 1;
            final Term[] heapTerms = new Term[size];
            String prettyprint = "<html><tt>" + (size > 1 ? "[" : "");
            for(int j =0 ; j < size; j++) {
                // TODO: there may still be work to do
                // what if we have a heap term, where the base heap lies deeper?
                final Term heap = step.subTerm().sub(j);
                heapTerms[j] = heap;
                lp.reset();
                try {
                    lp.printTerm(heap);
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
                prettyprint += (j>0 ? ", " : "")
                + LogicPrinter.escapeHTML(lp.toString().trim(), true);
            }
            prettyprint += (size > 1 ? "]" : "")+"</tt></html>";
            heaps[i++] = new TermStringWrapper(heapTerms, prettyprint);
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
         Label label = new Label(root, SWT.NONE);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
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
