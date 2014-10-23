package org.key_project.key4eclipse.common.ui.completion;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.gui.InvariantConfigurator;
import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleAbortException;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.LoopInvariantImpl;
import de.uka.ilkd.key.util.MiscTools;

/**
 * The {@link InteractiveRuleApplicationCompletion} to treat {@link WhileInvariantRule} in the Eclipse context.
 * @author Martin Hentschel
 */
public class LoopInvariantRuleCompletion extends AbstractInteractiveRuleApplicationCompletion {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canComplete(IBuiltInRuleApp app) {
      return de.uka.ilkd.key.gui.LoopInvariantRuleCompletion.checkCanComplete(app);
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
      
      private final LoopInvariantBuiltInRuleApp loopApp;
      
      private final Services services;
      
      private LoopInvariant inv;
     
      /**
       * Constructor.
       * @param app The DefaultBuiltInRuleApp to be completed.
       * @param goal The Goal where the app will later be applied to.
       * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
       */
      public Perform(IBuiltInRuleApp app, Goal goal, boolean forced) {
         super(app, goal, forced);
         
         services = goal.proof().getServices();
         
         loopApp = (LoopInvariantBuiltInRuleApp) app.tryToInstantiate(goal);
         
         inv = loopApp.getInvariant();
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getWindowTitle() {
         return "Invariant Configurator";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getTitle() {
         return "Invariant Configurator";
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createControl(Composite root) {
         final While loop = loopApp.getLoopStatement();
         if(inv == null) {
          MethodFrame mf = JavaTools.getInnermostMethodFrame(loopApp.programTerm().javaBlock(), services);
          
          inv = new LoopInvariantImpl(loop,
                                     mf == null ? null : mf.getProgramMethod(),
                                     mf == null || mf.getProgramMethod() == null ? 
                                           null : mf.getProgramMethod().getContainerType(),
                                     mf == null ? null : MiscTools.getSelfTerm(JavaTools.getInnermostMethodFrame(
                                              loopApp.programTerm().javaBlock(), services),
                                           services),
                                     null);
            try {
             inv = InvariantConfigurator.getInstance().getLoopInvariant(inv,
                     services, false, loopApp.getHeapContext()); 
            } catch (RuleAbortException e) {
            }
         } else {
            boolean requiresVariant = loopApp.variantRequired()
                  && !loopApp.variantAvailable();
          if (!isForced() || !loopApp.invariantAvailable() || requiresVariant) {
              try {
                  inv = InvariantConfigurator.getInstance().getLoopInvariant(
                          inv, services, requiresVariant, loopApp.getHeapContext());
              } catch (RuleAbortException e) {
              }
          }
         }
            
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
         if(inv != null && isForced()) {
            services.getSpecificationRepository().addLoopInvariant(inv);
         }
         return inv == null ? null : loopApp.setLoopInvariant(inv);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
      }
   }
}
