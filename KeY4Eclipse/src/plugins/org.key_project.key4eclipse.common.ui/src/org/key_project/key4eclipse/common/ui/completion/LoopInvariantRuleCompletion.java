package org.key_project.key4eclipse.common.ui.completion;

import java.io.StringReader;
import java.io.StringWriter;
import java.util.Map;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.speclang.LoopInvariant;

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
      //private Text invariantText = null;
      private DefaultTermParser parser = new DefaultTermParser();
      private Services services = getGoal().proof().getServices();
      private TabFolder editorTab = null;
      
      
      
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
       * extracts loop from app
       * @author Anna Marie Filighera
       * @return complete loop as String
       */
      private String getLoopText() {
         StringWriter writer = new StringWriter();
         String text = "";
         LoopInvariantBuiltInRuleApp loopApp = (LoopInvariantBuiltInRuleApp) getApp();
         try {
            loopApp.getLoopStatement().prettyPrint(new PrettyPrinter(writer));
            text = writer.toString();
         } catch (Exception e) {
            text = loopApp.getLoopStatement().toSource();
         } 
         return text.trim();
      }
      
      /**
       * parses input text and updates status reports accordingly
       * @author Anna Marie Filighera
       * @param input - text to be parsed
       * @param sortType - Sort of input text
       * @param status - status label to be updated
       * @return
       */
      private Term parseInputText(Text input, Sort sortType, Label status){
         Term result = null;
         try {
            result = parser.parse(
               new StringReader(input.getText()), sortType,
               services, services.getNamespaces(),
               MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap());
            status.setText("OK");
         }  catch(Exception e){
            status.setText(e.getMessage());
         }
         return result;
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
         
         //Set up right column:
         Composite stateColumn = new Composite(root, SWT.NO_BACKGROUND);
         stateColumn.setLayout(vertlayout);
         
         //Set up loop preview:
         Label code = new Label(stateColumn, SWT.BORDER);
         Font monospace = JFaceResources.getFont(JFaceResources.TEXT_FONT);
         code.setFont(monospace);
         code.setBackground(root.getDisplay().getSystemColor(SWT.COLOR_WHITE));
         code.setText(getLoopText());
         
         //Set up state view:
         Group invStatusGrp = new Group(stateColumn, SWT.SHADOW_IN);
         invStatusGrp.setLayout(vertlayout);
         invStatusGrp.setText("Invariant - Status:");
         invariantStatus = new Label(invStatusGrp, SWT.WRAP);
         invariantStatus.setText("Ok");

         Group modStatusGrp = new Group(stateColumn, SWT.SHADOW_IN);
         modStatusGrp.setLayout(vertlayout);
         modStatusGrp.setText("Modifies - Status:");
         modifiesStatus = new Label(modStatusGrp, SWT.WRAP);
         modifiesStatus.setText("Ok");

         Group varStatusGrp = new Group(stateColumn, SWT.SHADOW_IN);
         varStatusGrp.setLayout(vertlayout);
         varStatusGrp.setText("Variant - Status:");
         variantStatus = new Label(varStatusGrp, SWT.WRAP);
         variantStatus.setText("Ok");
         
         //Set up right column
         Composite rightColumn = new Composite(root, SWT.NO_BACKGROUND);
         rightColumn.setLayout(vertlayout);
         //TODO: register a listener to the TabFolder so we can see what the user is looking at.
         editorTab = new TabFolder(rightColumn, SWT.TOP);
         
         //get the initial state of the text fields.
         LoopInvariantBuiltInRuleApp loopApp = ((LoopInvariantBuiltInRuleApp) getApp()).tryToInstantiate(getGoal());
         LoopInvariant loopInv = loopApp.getInvariant();

         Map<LocationVariable,Term> atPres = loopInv.getInternalAtPres();
         String invariantString = "unable to load";
         String modifiesString = "unable to load";
         String variantString = "unable to load";
         for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            Term i = loopInv.getInvariant(heap, loopInv.getInternalSelfTerm(), atPres, services);
            Term modifies = loopInv.getModifies(heap, loopInv.getInternalSelfTerm(), atPres, services);

            if (i != null) {
               invariantString = ProofSaver.printTerm(i,  services, true).toString();
            }
            
            if (modifies != null) {
               modifiesString = ProofSaver.printTerm(modifies,  services, true).toString();
            }
         }
         
         Term variant = loopInv.getVariant(loopInv.getInternalSelfTerm(), atPres, services);
         if (variant != null) {
            variantString = ProofSaver.printTerm(variant, services, true).toString();
         }
         
         //Set up initial Tab
         addTab(invariantString, modifiesString, variantString, 0, editorTab);
         // set up store button
         Button store = new Button(rightColumn, SWT.PUSH);
         store.setText("Store");
         
         store.addSelectionListener(new SelectionAdapter(){
            // adds new tab 
            @Override
            public void widgetSelected(SelectionEvent e) {
               //TODO
               int currentTabID = editorTab.getSelectionIndex();
               //assert(editorTab.getSelection().length == 1);
               TabItem currentTab = editorTab.getSelection()[0];//Might fail if !=1 items selected.
               Composite textCtr = (Composite) currentTab.getControl();
               int amountTabs = editorTab.getItemCount();
               addTab(
                  ((Text)((Group)textCtr.getChildren()[0]).getChildren()[0]).getText(),
                  ((Text)((Group)textCtr.getChildren()[1]).getChildren()[0]).getText(),
                  ((Text)((Group)textCtr.getChildren()[2]).getChildren()[0]).getText(),
                  amountTabs, editorTab);
            }
         });
         //Potential expansion: Discard rule application if Completion dialog was aborted.
         //TODO: Status tab should be updated after GUI setup, and after tab switch also.
      }
      
      /**
       * @author Viktor Pfanschilling
       * @param invariant - invariant text of the tab
       * @param modifies - modifies text of the tab
       * @param variants - variants text of the tab
       * @param id - id of the new tab
       * @param parent - where to attach the item
       * @return the generated TabItem
       */
      private Control addTab(String invariant, String modifies, String variants, int id, TabFolder parent){
         FillLayout vertlayout = new FillLayout(SWT.VERTICAL);
         //add a tab item
         TabItem t = new TabItem (parent, SWT.NONE);
         t.setText("inv " + id);
         //inside, place a composite containing three groups (for pretty frames) with a Text item each.
         Composite textContainer = new Composite(parent, SWT.NO_BACKGROUND);
         t.setControl(textContainer);
         Group inv1 = new Group(textContainer, SWT.SHADOW_IN);
         Text invariantT = new Text(inv1, SWT.MULTI);
         Group mod1 = new Group(textContainer, SWT.SHADOW_IN);
         Text modifiesT = new Text(mod1, SWT.MULTI);
         Group var1 = new Group(textContainer, SWT.SHADOW_IN);
         Text variantsT = new Text(var1, SWT.MULTI);
         textContainer.setLayout(vertlayout);
         inv1.setLayout(vertlayout);
         mod1.setLayout(vertlayout);
         var1.setLayout(vertlayout);
         inv1.setText("invariant");
         invariantT.setText(invariant);
         mod1.setText("modifies");
         modifiesT.setText(modifies);
         var1.setText("variants");
         variantsT.setText(variants);
         
         //add listeners.
         invariantT.addModifyListener(new ModifyListener(){
            public void modifyText(ModifyEvent event) {
               Text text = (Text) event.widget;
               Term inv = parseInputText(text, Sort.FORMULA, invariantStatus);
            }
         });
         
         modifiesT.addModifyListener(new ModifyListener(){
            public void modifyText(ModifyEvent event) {
               Text text = (Text) event.widget;
               Sort modSort = services.getTypeConverter().getLocSetLDT().targetSort();
               Term mod = parseInputText(text, modSort, modifiesStatus);
            }
         });
         
         variantsT.addModifyListener(new ModifyListener(){
            public void modifyText(ModifyEvent event) {
               Text text = (Text) event.widget;
               Sort varSort = services.getTypeConverter().getIntegerLDT().targetSort();
               Term var = parseInputText(text, varSort, variantStatus);
            }
         });
         
         return textContainer;
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
