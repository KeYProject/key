package org.key_project.key4eclipse.common.ui.completion;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.TabFolder;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;

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
      
      private Composite root = null;
      /**
       * Constructor.
       * @param app The DefaultBuiltInRuleApp to be completed.
       * @param goal The Goal where the app will later be applied to.
       * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
       */
      public Perform(IBuiltInRuleApp app, Goal goal, boolean forced) {
         super(app, goal, forced);
         setErrorMessage("Functionality is not available yet.");
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
         this.root = root;
         
         FillLayout horlayout = new FillLayout(SWT.HORIZONTAL);
         root.setLayout(horlayout);
         FillLayout vertlayout = new FillLayout(SWT.VERTICAL);
         
         //Set up loop preview:
         Composite codeColumn = new Composite(root, SWT.NO_BACKGROUND);
         codeColumn.setLayout(vertlayout);
         Label code = new Label(codeColumn, SWT.BORDER);
         Font monospace = JFaceResources.getFont(JFaceResources.TEXT_FONT);//new Font(root.getDisplay(), "Monospaced", 10, SWT.NORMAL);
         code.setFont(monospace);
         code.setBackground(root.getDisplay().getSystemColor(SWT.COLOR_WHITE));
         code.setText("This is example soure code.\n  This should align nicely.\n  Lorem ipsum and so forth. ");
         
         //Set up state view:
         Group stateColumn = new Group(root, SWT.SHADOW_IN);
         stateColumn.setLayout(vertlayout);
         Label invStatus = new Label(stateColumn, SWT.BORDER);
         invStatus.setText("state here");
         TabFolder modStatus = new TabFolder(stateColumn, SWT.TOP);
         TabFolder variantStatus = new TabFolder(stateColumn, SWT.TOP);
         
         //set up invariantEditor:
         Group invariantColumn = new Group(root, SWT.SHADOW_IN);
         invariantColumn.setLayout(vertlayout);
         Label d = new Label(invariantColumn, SWT.BORDER);
         d.setText("More Stuff!");
         //TabFolder invariants = new TabFolder(stateColumn, SWT.TOP);
         TabFolder modifies = new TabFolder(stateColumn, SWT.TOP);
         TabFolder variant = new TabFolder(stateColumn, SWT.TOP);
         
         
         //root.layout(true, true);
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
         root.dispose();
      }
   }
}
