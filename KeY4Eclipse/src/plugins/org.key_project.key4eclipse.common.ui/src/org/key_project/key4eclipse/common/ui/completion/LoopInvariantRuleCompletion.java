package org.key_project.key4eclipse.common.ui.completion;

import java.io.StringReader;
import java.io.StringWriter;
import java.util.LinkedHashMap;
import java.util.Map;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.events.ControlAdapter;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.TabFolder;
import org.eclipse.swt.widgets.TabItem;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.widgets.SharedScrolledComposite;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.gui.InteractiveRuleApplicationCompletion;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.InfFlowSpec;

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
      private DefaultTermParser parser = new DefaultTermParser();
      private Services services = getGoal().proof().getServices();
      private TabFolder editorTab = null;
      private LocationVariable[] heaps = null;
      
      
      /**
       * Constructor.
       * @param app The DefaultBuiltInRuleApp to be completed.
       * @param goal The Goal where the app will later be applied to.
       * @param forced A boolean indicating if the rule should be applied without any additional interaction from the user provided that the application object can be made complete automatically.
       */
      public Perform(IBuiltInRuleApp app, Goal goal, boolean forced) {
         super(app, goal, forced);
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
       * {@inheritDoc}
       */
      @Override
      public void createControl(Composite parent) {
         root = new SashForm(parent, SWT.NONE);
         
         //TODO: For reference tests, see DependencyContractCompletion.java
         //TODO: cleanup layout
         //TODO: All the text/label things should be set to WRAP
         //fillData.horizontalAlignment = SWT.FILL;
         
         //Set up right column:
         Composite stateColumn = new Composite(root, SWT.NONE);
         stateColumn.setLayout(new GridLayout(1, false));
//         stateColumn.setLayoutData(new GridData(GridData.FILL_BOTH));
         
         //Set up loop preview:
         Text code = new Text(stateColumn, SWT.READ_ONLY | SWT.WRAP);
         code.setLayoutData(new GridData(GridData.FILL_BOTH));
         Font monospace = JFaceResources.getFont(JFaceResources.TEXT_FONT);
         code.setFont(monospace);
         code.setText(getLoopText());
         
         //Set up state views:
         Group invStatusGrp = new Group(stateColumn, SWT.NONE);
         invStatusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
         invStatusGrp.setLayout(new FillLayout());
         invStatusGrp.setText("Invariant - Status:");
         invariantStatus = new Label(invStatusGrp, SWT.WRAP);
         invariantStatus.setText("Ok");

         Group modStatusGrp = new Group(stateColumn, SWT.NONE);
         modStatusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
         modStatusGrp.setLayout(new FillLayout());
         modStatusGrp.setText("Modifies - Status:");
         modifiesStatus = new Label(modStatusGrp, SWT.WRAP);
         modifiesStatus.setText("Ok");

         Group varStatusGrp = new Group(stateColumn, SWT.NONE);
         varStatusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
         varStatusGrp.setLayout(new FillLayout());
         varStatusGrp.setText("Variant - Status:");
         variantStatus = new Label(varStatusGrp, SWT.WRAP);
         variantStatus.setText("Ok");
         
         //Set up right column
         Composite inputColumn = new Composite(root, SWT.NONE);
         inputColumn.setLayout(new GridLayout(1, false));
         editorTab = new TabFolder(inputColumn, SWT.TOP);
         editorTab.setLayoutData(new GridData(GridData.FILL_BOTH));
         //this listener updates the state whenever tabs are switched.
         editorTab.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent event) {
               resetStateTab();
            }
         });
         // set up store button
         Button store = new Button(inputColumn, SWT.PUSH);
         store.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         store.setText("Store");
         store.addSelectionListener(new SelectionAdapter(){
            @Override
            public void widgetSelected(SelectionEvent e) {
               store(); // add new tab 
            }
         });
         
         //get the initial state of the text fields.
         LoopInvariantBuiltInRuleApp loopApp = ((LoopInvariantBuiltInRuleApp) getApp()).tryToInstantiate(getGoal());
         LoopInvariant loopInv = loopApp.getInvariant();

         Map<LocationVariable,Term> atPres = loopInv.getInternalAtPres();
         int heapCnt = services.getTypeConverter().getHeapLDT().getAllHeaps().size();
         heaps = new LocationVariable[heapCnt];
         String[] invariantStrings = new String[heapCnt];
         String[] modifiesStrings = new String[heapCnt];
         String variantString = "unable to load";
         int iter = 0;//iterator so we know where we're at.
         for(LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
            heaps[iter] = heap;
            Term invTerm = loopInv.getInvariant(heap, loopInv.getInternalSelfTerm(), atPres, services);
            Term modifies = loopInv.getModifies(heap, loopInv.getInternalSelfTerm(), atPres, services);
            if (invTerm != null) {
               invariantStrings[iter] = ProofSaver.printTerm(invTerm, services, true).toString();
            }
            
            if (modifies != null) {
               modifiesStrings[iter] = ProofSaver.printTerm(modifies, services, true).toString();
            }
            iter++;
         }
         
         Term variant = loopInv.getVariant(loopInv.getInternalSelfTerm(), atPres, services);
         if (variant != null) {
            variantString = ProofSaver.printTerm(variant, services, true).toString();
         }
         
         //Set up initial Tab
         addTab(invariantStrings, modifiesStrings, variantString, 0);
         
         resetStateTab();
         
         //TODO: Potential expansion: Discard rule application if Completion dialog was aborted.
         //This is probably not possible from within this class
      }
      
      /**
       * adds a copy of the currently selected specification
       */
      private void store(){
         //FIXME: doesn't *actually* store anything.
         int selectedSpec = editorTab.getSelectionIndex();
         int amountTabs = editorTab.getItemCount();
         String[] invSpecs = new String[heaps.length];
         String[] modSpecs = new String[heaps.length];
         String varSpec = getTextField(selectedSpec, 0, 2).getText();
         for (int i = 0; i < heaps.length; i++) {
            invSpecs[i] = getTextField(selectedSpec, i, 0).getText();
            modSpecs[i] = getTextField(selectedSpec, i, 1).getText();
         }
         addTab(invSpecs, modSpecs, varSpec, amountTabs);
      }

      /**
       * adds a new invariant tab to the specified TabFolder.
       * @author Viktor Pfanschilling
       * @param invariant - invariant text of the tab
       * @param modifies - modifies text of the tab
       * @param variant - variants text of the tab
       * @param id - id of the new tab
       * @return the generated TabItem's Composite
       */
      private Control addTab(String[] invariants, String[] modifies, String variant, int id) {
         //TODO: do not add as a tab, but add another Composite. DropDown menu to switch between specifications.
         
         //add a tab item
         TabItem tab = new TabItem(editorTab, SWT.NONE);
         tab.setText("inv " + id);
         
         //inside, place a composite containing three groups (for pretty frames) with a Text item each.
         final SharedScrolledComposite scrolledComposite = new SharedScrolledComposite(editorTab, SWT.H_SCROLL | SWT.V_SCROLL) {};
         scrolledComposite.setExpandHorizontal(true);
         scrolledComposite.setExpandVertical(true);
         
         Composite textContainer = new Composite(scrolledComposite, SWT.NONE);
         textContainer.setLayout(new GridLayout(1, false));
         scrolledComposite.setContent(textContainer);
         tab.setControl(scrolledComposite);
         tab.getParent().addControlListener(new ControlAdapter() {
            @Override
            public void controlResized(ControlEvent e) {
               scrolledComposite.reflow(true);
            }
         });
         //add a tab folder
         TabFolder heapTabs = new TabFolder(textContainer, SWT.TOP);
         heapTabs.setLayoutData(new GridData(GridData.FILL_BOTH));
         heapTabs.addSelectionListener(new SelectionAdapter() {
            public void widgetSelected(SelectionEvent event) {
               resetStateTab();
            }
         });
         int iter = 0;
         for(LocationVariable heap : heaps){
            TabItem heapTab = new TabItem(heapTabs, SWT.NONE);
            heapTab.setText(heap.toString());
            Composite modinvcontainer = new Composite(heapTabs, SWT.NONE);
            modinvcontainer.setLayout(new GridLayout(1, false));
            heapTab.setControl(modinvcontainer);
            
            //for all elems in heap, add a TabItem
            Group invariantGroup = new Group(modinvcontainer, SWT.NONE);
            Text invariantT = new Text(invariantGroup, SWT.V_SCROLL);
            invariantGroup.setLayout(new FillLayout());
            invariantGroup.setText("invariant");
            invariantGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
            invariantT.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));
            invariantT.setText(invariants[iter] != null ? invariants[iter] : "true");
            Group modifiesGroup = new Group(modinvcontainer, SWT.NONE);
            modifiesGroup.setLayout(new FillLayout());
            modifiesGroup.setText("modifies");
            modifiesGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
            Text modifiesT = new Text(modifiesGroup, SWT.V_SCROLL);
            modifiesT.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));
            modifiesT.setText(modifies[iter] != null? modifies[iter] : "allLocs");
            
            invariantT.addModifyListener(new ModifyListener(){
               public void modifyText(ModifyEvent event) {
                  updateErrorMessage();
                  resetInvariantState();
               }
            });
            
            modifiesT.addModifyListener(new ModifyListener(){
               public void modifyText(ModifyEvent event) {
                  updateErrorMessage();
                  resetModifiesState();
               }
            });
            iter++;
         }
         Group variantsGroup = new Group(textContainer, SWT.NONE);
         variantsGroup.setLayout(new FillLayout());
         variantsGroup.setText("variants");
         variantsGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
         Text variantsT = new Text(variantsGroup, SWT.V_SCROLL);
         variantsT.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));
         variantsT.setText(variant == null ? "" : variant);
         
         variantsT.addModifyListener(new ModifyListener(){
            public void modifyText(ModifyEvent event) {
               updateErrorMessage();
               resetVariantsState();
            }
         });
         
         return textContainer;
      }
      
      /**
       * resets the error message of the window. Tied to the finish button.
       * Call every time any of the texts of the
       * currently selected specification or the selection changes.
       * @author Viktor Pfanschilling
       */
      private void updateErrorMessage(){
         setErrorMessage(null);
         int i = 0;
         for (LocationVariable heap : heaps){
            Text wdgt = getTextField(-1, i, 0);
            Term invariantTerm = parseInputText(wdgt.getText(), Sort.FORMULA, null);
            wdgt = getTextField(-1, i, 1);
            Sort modSort = services.getTypeConverter().getLocSetLDT().targetSort();
            Term modifiesTerm = parseInputText(wdgt.getText(), modSort, null);
            if (invariantTerm == null)setErrorMessage("Error in current specification: " + heap.toString() + " / invariant");
            if (modifiesTerm == null)setErrorMessage("Error in current specification: " + heap.toString() + " / modifies");
            i++;
         }
         Term variantTerm = resetVariantsState();
         if (variantTerm == null) setErrorMessage("Error in current specification: variant");
         return;
      }
      
      /**
       * resets the state text for all three input fields.
       * @author Viktor Pfanschilling
       */
      private void resetStateTab(){
         updateErrorMessage();
         TabItem[] selectedTabs = editorTab.getSelection();
         if (selectedTabs.length == 1){
            resetInvariantState();
            resetModifiesState();
            resetVariantsState();
         }
      }
      
      /**
       * resets the state text for the user-specified invariant
       * @author Viktor Pfanschilling
       * @param wdgt - the widget containing the user input
       */
      private Term resetInvariantState(){
         Text wdgt = getTextField(-1, -1, 0);
         return parseInputText(wdgt.getText(), Sort.FORMULA, invariantStatus);
      }
      
      /**
       * resets the state text for the user-specified modifies field
       * @author Viktor Pfanschilling
       * @param wdgt - the widget containing the user input
       */
      private Term resetModifiesState(){
         Text wdgt = getTextField(-1, -1, 1);
         Sort modSort = services.getTypeConverter().getLocSetLDT().targetSort();
         return parseInputText(wdgt.getText(), modSort, modifiesStatus);
      }
      
      /**
       * resets the state text for the user-specified variants
       * @author Viktor Pfanschilling
       * @param wdgt - the widget containing the user input
       */
      private Term resetVariantsState(){
         Text wdgt = getTextField(-1, -1, 2);
         Sort varSort = services.getTypeConverter().getIntegerLDT().targetSort();
         return parseInputText(wdgt.getText(), varSort, variantStatus);
      }
      
      /**
       * parses input text and updates status reports accordingly
       * @author Anna Marie Filighera
       * @param input - text to be parsed
       * @param sortType - Sort of input text
       * @param status - status label to be updated, or null for none
       * @return
       */
      private Term parseInputText(String input, Sort sortType, Label status){
         Term result = null;
         try {
            result = parser.parse(
               new StringReader(input), sortType,
               services, services.getNamespaces(),
               MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap());
            if (status != null) status.setText("OK");
         }  catch(Exception e){
            if (status != null) status.setText(e.getMessage());
         }
         return result;
      }

      /**
       * @param specification - the big tab folder's tab in we want; -1 is current selection
       * @param heap - the small tab folder's tab we want, or the heap index in question; -1 is current selection
       * @param textField - 0 for invariant, 1 for modifies, 2 for variant
       * @return the Text widget containing the specification.
       */
      private Text getTextField(int specification, int heap, int textField){
         if (specification == -1) {
            specification = editorTab.getSelectionIndex();
         }
         TabItem tab = editorTab.getItem(specification);
         ScrolledComposite scrolledComposite = (ScrolledComposite) tab.getControl();
         Composite txtcontainer = (Composite) scrolledComposite.getContent();
         if (textField == 2) {
            Group vargrp = (Group)txtcontainer.getChildren()[1];
            return (Text)vargrp.getChildren()[0];
         }
         TabFolder tfld = (TabFolder)txtcontainer.getChildren()[0];
         if (heap == -1) heap = tfld.getSelectionIndex(); // TODO: NEVER DO; ALWAYS IN TWO LINES WITH {}!! HERE AND EVERYWHERE!
         Composite modinvcontainer = (Composite)(tfld.getItem(heap).getControl());
         Group modOrVarGrp = (Group)(modinvcontainer.getChildren()[textField]);
         Text wdgt = (Text)modOrVarGrp.getChildren()[0];
         return wdgt;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
         //TODO: Check for error messages, return null if there's a problem
         LoopInvariantBuiltInRuleApp loopApp = ((LoopInvariantBuiltInRuleApp) getApp()).tryToInstantiate(getGoal());
         Map<LocationVariable, Term> invMap = new LinkedHashMap<LocationVariable, Term>();
         Map<LocationVariable, Term> modMap = new LinkedHashMap<LocationVariable, Term>();
         int i = 0;
         //for every heap:
         for (LocationVariable heap : heaps) {
            //get the invariant and modify terms
            Text wdgt = getTextField(-1, i, 0);
            Term invariantTerm = parseInputText(wdgt.getText(), Sort.FORMULA, null);
            if (invariantTerm == null) {
               return null;
            }
            wdgt = getTextField(-1, i, 1);
            Sort modSort = services.getTypeConverter().getLocSetLDT().targetSort();
            Term modifiesTerm = parseInputText(wdgt.getText(), modSort, null);
            if (modifiesTerm == null) {
               return null;
            }
            invMap.put(heap, invariantTerm);
            modMap.put(heap, modifiesTerm);
            if (invariantTerm == null || modifiesTerm == null) {
               return null;
            }
            i++;
         }
         //get the variant
         Term variantTerm = resetVariantsState();
         if (variantTerm == null) {
            return null;
         }
         
         //FIXME: InfFlowSpecs are currently not implemented, thus there's little point in writing a UI for them.
         //The InfFlowSpecs code here does not actually do anything.
         Map<LocationVariable, ImmutableList<InfFlowSpec>> infFlowSpecs = new LinkedHashMap<LocationVariable, ImmutableList<InfFlowSpec>>();
         
         //return the new Invariant
         LoopInvariant newInvariant = loopApp.getInvariant().configurate(invMap, modMap, infFlowSpecs, variantTerm);
         return loopApp.setLoopInvariant(newInvariant);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
         //TODO: Is there more to do here?
         root.dispose(); // TODO: In theory the UI disposes contained elements automatically. What needs to be disposed manually are provider, fonts, images, colors, ... Also ensure that all added listeners are removed.
      }
   }
}
