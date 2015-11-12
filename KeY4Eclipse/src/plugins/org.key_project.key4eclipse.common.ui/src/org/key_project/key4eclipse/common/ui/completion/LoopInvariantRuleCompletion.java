package org.key_project.key4eclipse.common.ui.completion;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;

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
      private Label invariantStatus = null;
      private Label modifiesStatus = null;
      private Label variantStatus = null;
      private Text invariantText = null;
      
      
      
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
         invariantStatus = new Label(stateColumn, SWT.BORDER);
         invariantStatus.setText("Invariant Status\nOk");
         
         TabFolder modifiesStatusTab = new TabFolder(stateColumn, SWT.TOP);
         modifiesStatus = (Label)addTextTabItem("heap", "Modifies - Status:\nOk", false, modifiesStatusTab);
         
         TabFolder variantStatusTab = new TabFolder(stateColumn, SWT.TOP);
         variantStatus = (Label)addTextTabItem("heap", "Variant status ok", false, variantStatusTab);
         
         
         //set up invariantEditor:
         Group invariantColumn = new Group(root, SWT.SHADOW_IN);
         invariantColumn.setLayout(vertlayout);
         TabFolder invariants = new TabFolder(invariantColumn, SWT.TOP);
         invariantText = (Text)addTextTabItem("inv 0", "some invariant text, probably monospace", true, invariants);
         TabFolder modifies = new TabFolder(invariantColumn, SWT.TOP);
         Text modifiesText = (Text)addTextTabItem("heap", "Modifies\nEmpty", true, modifies);
         TabFolder variant = new TabFolder(invariantColumn, SWT.TOP);
         Text invariantText = (Text)addTextTabItem("heap", "Variant: someCode", true, variant);
         
         modifiesText.addModifyListener(new ModifyListener(){
            public void modifyText(ModifyEvent event) {
               Text text = (Text) event.widget;
               //do something with the text.
            }
         });
         
         invariantText.addModifyListener(new ModifyListener(){
            public void modifyText(ModifyEvent event) {
               Text text = (Text) event.widget;
               //do something with the text.
            }
         });
      }
      
      /**
       * @param head - title of the tabitem
       * @param body - text within the tabitem
       * @param writable - is the text user-editable
       * @param parent - where to attach the item
       * @return the generated TabItem
       */
      private Control addTextTabItem(String head, String body, boolean writable, TabFolder parent){
         TabItem t = new TabItem (parent, SWT.NONE);
         t.setText(head);
         Control c = null;
         if (writable){
            Text l = new Text(parent, SWT.MULTI);
            l.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));
            l.setText(body);
            c = l;
         } else {
            Label l = new Label(parent, SWT.NONE);
            l.setText(body);
            c = l;
         }
         t.setControl(c);
         return c;
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
