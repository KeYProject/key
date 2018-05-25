package org.key_project.key4eclipse.common.ui.completion;

import java.io.StringReader;
import java.io.StringWriter;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Vector;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.events.*;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.*;
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
import de.uka.ilkd.key.speclang.LoopSpecification;
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
      
      /**
       * The Composite in the wizard this dialog is attached to.
       */
      private Composite root = null;
      /**
       * Displays the status of the invariant specification the user is looking at.
       */
      private Label invariantStatus = null;
      /**
       * Displays the status of the modifies specification the user is looking at.
       */
      private Label modifiesStatus = null;
      /**
       * Displays the status of the variant specification the user is looking at.
       */
      private Label variantStatus = null;
      /**
       * The services in use.
       */
      private Services services = getGoal().proof().getServices();
      /**
       * The heaps this object is dealing with.
       */
      private LocationVariable[] heaps = null;
      /**
       * The specSwitchComposite, alternatively displaying widgets for one of the specifications.
       */
      private Composite specSwitchComposite = null;
      /**
       * The layout of specSwitchComposite. onTopControl sets the currently visible specification
       */
      private StackLayout stackLayout = null;
      /**
       * The Combo box that contains references to all the alternative specifications.
       */
      private Combo specSelector = null;
      /**
       * The Store Button.
       */
      private Button store = null;
      
      
      /////////////// The listeners and attachment points for Listeners are just stored here for cleanup ///////////////
      
      /**
       * The listener that causes specification selections.
       */
      private SelectionAdapter specSelectListener = new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            switchPage(specSelector.getSelectionIndex());
         }
      };
      /**
       * The listener that handles store events.
       */
      private SelectionAdapter storeListener = new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            store(); // add new tab 
         }
      };
      /**
       * the TabFolders that contain the specification for one heap.
       */
      private Vector<TabFolder> heapTabFolders = new Vector<>();
      /**
       * The listeners for the heapTabFolders, handling the update of the error panel.
       */
      private SelectionAdapter heapTabsListener = new SelectionAdapter() {
         public void widgetSelected(SelectionEvent e) {
            resetStateTab();
         }
      };
      /**
       * List of Control Elements that have had Control Listeners attached.
       */
      private Vector<Control> cListenerParents = new Vector<>();
      /**
       * List of listeners, corresponding to cListenerParents.
       */
      private Vector<ControlListener> cListeners = new Vector<>();
      /**
       * Vector of elements a modifyListener has been attached to.
       */
      private Vector<Text> mListenerParents = new Vector<>();
      /**
       * Listener to be called when input text is modified.
       */
      private ModifyListener modifyListener = new ModifyListener() {
         public void modifyText(ModifyEvent e) {
            resetStateTab();
         }
      };
      
      
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
       * extracts loop from app.
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
       * @param parent The composite to which to attach the Group
       * @param text the header text the state view should have
       * @return the Label that is meant for the actual state message
       */
      private Label mkStateView(Composite parent, String text) {
         Group statusGrp = new Group(parent, SWT.NONE);
         statusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
         statusGrp.setLayout(new FillLayout());
         statusGrp.setText(text);
         Label status = new Label(statusGrp, SWT.WRAP);
         status.setText("Ok");
         return status;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void createControl(Composite parent) {
         root = new SashForm(parent, SWT.NONE);
         
         //Set up right column:
         Composite stateColumn = new Composite(root, SWT.NONE);
         stateColumn.setLayout(new GridLayout(1, false));
         
         //Set up loop preview:
         Text code = new Text(stateColumn, SWT.READ_ONLY | SWT.WRAP);
         code.setLayoutData(new GridData(GridData.FILL_BOTH));
         Font monospace = JFaceResources.getFont(JFaceResources.TEXT_FONT);
         code.setFont(monospace);
         code.setText(getLoopText());
         
         //Set up state views:
         invariantStatus = mkStateView(stateColumn, "Invariant - Status:");
         modifiesStatus = mkStateView(stateColumn, "Modifies - Status:");
         variantStatus = mkStateView(stateColumn, "Variant - Status:");
         
         //Set up right column
         final Composite inputColumn = new Composite(root, SWT.NONE);
         inputColumn.setLayout(new GridLayout(1, false));
         
         cListeners.add(new ControlAdapter() {
            @Override
            public void controlResized(ControlEvent e) {
               inputColumn.layout();
            }
         });
         cListenerParents.add(inputColumn);
         cListenerParents.lastElement().addControlListener(cListeners.lastElement());
         
         //selector drop down
         specSelector = new Combo(inputColumn, SWT.DROP_DOWN | SWT.READ_ONLY);
         specSelector.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         specSelector.addSelectionListener(specSelectListener);
         
         specSwitchComposite = new Composite(inputColumn, SWT.NONE);
         specSwitchComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
         stackLayout = new StackLayout();
         specSwitchComposite.setLayout(stackLayout);
         
         // set up store button
         store = new Button(inputColumn, SWT.PUSH);
         store.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         store.setText("Store");
         store.addSelectionListener(storeListener);
         
         //get the initial state of the text fields.
         LoopInvariantBuiltInRuleApp loopApp = ((LoopInvariantBuiltInRuleApp) getApp()).tryToInstantiate(getGoal());
         LoopSpecification loopInv = loopApp.getSpec();

         Map<LocationVariable, Term> atPres = loopInv.getInternalAtPres();
         int heapCnt = services.getTypeConverter().getHeapLDT().getAllHeaps().size();
         heaps = new LocationVariable[heapCnt];
         String[] invariantStrings = new String[heapCnt];
         String[] modifiesStrings = new String[heapCnt];
         String variantString = "unable to load";
         int iter = 0; //iterator so we know where we're at.
         for (LocationVariable heap : services.getTypeConverter().getHeapLDT().getAllHeaps()) {
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
         //select it
         specSelector.select(0);
         switchPage(0);
         
         //FIXME: Rule will be applied even if Completion dialog was aborted.
         //This is probably not preventable from within this class
      }
      
      /**
       * manually switches to another specification, as if user input happened.
       * @param id the id to which to switch
       */
      private void switchPage(int id) {
         //put the page on top
         stackLayout.topControl = (Composite) specSwitchComposite.getChildren()[id];
         specSwitchComposite.layout();
         //update the error messages.
         resetStateTab();
      }
      
      /**
       * adds a copy of the currently selected specification.
       */
      private void store() {
         //Just add another specification.
         //finish() and the framework take care of putting the spec to more persistent memory.
         //At least - as in KeY - the currently selected spec.
         int selectedSpec = getSelection();
         int amountTabs = specSwitchComposite.getChildren().length;
         String[] invSpecs = new String[heaps.length];
         String[] modSpecs = new String[heaps.length];
         String varSpec = getTextField(selectedSpec, 0, 2).getText();
         for (int i = 0; i < heaps.length; i++) {
            invSpecs[i] = getTextField(selectedSpec, i, 0).getText();
            modSpecs[i] = getTextField(selectedSpec, i, 1).getText();
         }
         //amount of tabs coincides to be the ID of the one we create.
         addTab(invSpecs, modSpecs, varSpec, amountTabs);
         specSelector.select(amountTabs);
         switchPage(amountTabs);
      }

      /**
       * adds a new invariant tab to the specified TabFolder.
       * @author Viktor Pfanschilling
       * @param invariants - invariant texts of the tab
       * @param modifies - modifies texts of the tab
       * @param variant - variants text of the tab
       * @param id - id of the new tab
       * @return the generated Composite
       */
      private Composite addTab(String[] invariants, String[] modifies, String variant, int id) {
         //add a item in the drop down
         specSelector.add("inv " + id);
         
         //create a scrolledComposite...
         final SharedScrolledComposite scrolledComposite = new SharedScrolledComposite(specSwitchComposite, SWT.H_SCROLL | SWT.V_SCROLL) { };
         scrolledComposite.setExpandHorizontal(true);
         scrolledComposite.setExpandVertical(true);
         //add layout to scrolledComposite?
         
         //... containing a composite...
         Composite textContainer = new Composite(scrolledComposite, SWT.NONE);
         textContainer.setLayout(new GridLayout(1, false));
         scrolledComposite.setContent(textContainer);
         cListeners.add(new ControlAdapter() {
            @Override
            public void controlResized(ControlEvent e) {
               scrolledComposite.reflow(true);
            }
         });
         cListenerParents.add(specSwitchComposite);
         cListenerParents.lastElement().addControlListener(cListeners.lastElement());
         //... add a tab folder for heap-sensitive Invariants ...
         TabFolder heapTabs = new TabFolder(textContainer, SWT.TOP);
         heapTabs.setLayoutData(new GridData(GridData.FILL_BOTH));
         int iter = 0;
         for (LocationVariable heap : heaps) {
            //for all elems in heap, add a TabItem
            TabItem heapTab = new TabItem(heapTabs, SWT.NONE);
            heapTab.setText(heap.toString());
            Composite modinvcontainer = new Composite(heapTabs, SWT.NONE);
            modinvcontainer.setLayout(new GridLayout(1, false));
            heapTab.setControl(modinvcontainer);
            
            //Groups are for pretty frames.
            Group invariantGroup = new Group(modinvcontainer, SWT.NONE);
            Text invariantT = new Text(invariantGroup, SWT.V_SCROLL | SWT.WRAP);
            invariantGroup.setLayout(new FillLayout());
            invariantGroup.setText("invariant");
            invariantGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
            invariantT.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));
            if (invariants[iter] == null) {
               invariants[iter] = "true";
            }
            invariantT.setText(invariants[iter]);
            Group modifiesGroup = new Group(modinvcontainer, SWT.NONE);
            modifiesGroup.setLayout(new FillLayout());
            modifiesGroup.setText("modifies");
            modifiesGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
            Text modifiesT = new Text(modifiesGroup, SWT.V_SCROLL | SWT.WRAP);
            modifiesT.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));
            if (modifies[iter] == null) {
               modifies[iter] = "allLocs";
            }
            modifiesT.setText(modifies[iter]);
            
            mListenerParents.add(invariantT);
            invariantT.addModifyListener(modifyListener);
            
            mListenerParents.add(modifiesT);
            modifiesT.addModifyListener(modifyListener);
            
            iter++;
         }
         heapTabFolders.add(heapTabs);
         heapTabs.addSelectionListener(heapTabsListener);
         Group variantsGroup = new Group(textContainer, SWT.NONE);
         variantsGroup.setLayout(new FillLayout());
         variantsGroup.setText("variants");
         variantsGroup.setLayoutData(new GridData(GridData.FILL_BOTH));
         Text variantsT = new Text(variantsGroup, SWT.V_SCROLL | SWT.WRAP);
         variantsT.setFont(JFaceResources.getFont(JFaceResources.TEXT_FONT));
         if (variant == null) {
            variant = "";
         }
         variantsT.setText(variant);
         
         mListenerParents.add(variantsT);
         variantsT.addModifyListener(modifyListener);
         
         return scrolledComposite;
      }
      
      /**
       * resets the error message of the window. Tied to the finish button.
       * Call every time any of the texts of the
       * currently selected specification or the selection changes.
       * @author Viktor Pfanschilling
       */
      private void updateErrorMessage() {
         setErrorMessage(null);
         int i = 0;
         for (LocationVariable heap : heaps) {
            Text wdgt = getTextField(-1, i, 0);
            Term invariantTerm = parseInputText(wdgt.getText(), Sort.FORMULA, null);
            wdgt = getTextField(-1, i, 1);
            Sort modSort = services.getTypeConverter().getLocSetLDT().targetSort();
            Term modifiesTerm = parseInputText(wdgt.getText(), modSort, null);
            if (invariantTerm == null) {
               setErrorMessage("Error in current specification: " + heap.toString() + " / invariant");
            }
            if (modifiesTerm == null) {
               setErrorMessage("Error in current specification: " + heap.toString() + " / modifies");
            }
            i++;
         }
         Term variantTerm = resetVariantsState();
         if (variantTerm == null) {
            setErrorMessage("Error in current specification: variant");
         }
         return;
      }
      
      /**
       * resets the state text for all three input fields.
       * @author Viktor Pfanschilling
       */
      private void resetStateTab() {
         updateErrorMessage();
         resetInvariantState();
         resetModifiesState();
         resetVariantsState();
      }
      
      /**
       * resets the state text for the user-specified invariant.
       * @author Viktor Pfanschilling
       * @return the invariant term
       */
      private Term resetInvariantState() {
         Text wdgt = getTextField(-1, -1, 0);
         return parseInputText(wdgt.getText(), Sort.FORMULA, invariantStatus);
      }
      
      /**
       * resets the state text for the user-specified modifies field.
       * @author Viktor Pfanschilling
       * @return the modifies term
       */
      private Term resetModifiesState() {
         Text wdgt = getTextField(-1, -1, 1);
         Sort modSort = services.getTypeConverter().getLocSetLDT().targetSort();
         return parseInputText(wdgt.getText(), modSort, modifiesStatus);
      }
      
      /**
       * resets the state text for the user-specified variants.
       * @author Viktor Pfanschilling
       * @return the variant term
       */
      private Term resetVariantsState() {
         Text wdgt = getTextField(-1, -1, 2);
         Sort varSort = services.getTypeConverter().getIntegerLDT().targetSort();
         return parseInputText(wdgt.getText(), varSort, variantStatus);
      }
      
      /**
       * parses input text and updates status reports accordingly.
       * @author Anna Marie Filighera
       * @param input - text to be parsed
       * @param sortType - Sort of input text
       * @param status - status label to be updated, or null for none
       * @return the Term parsed from the input, given the specification
       */
      private Term parseInputText(String input, Sort sortType, Label status) {
         Term result = null;
         try {
            DefaultTermParser parser = new DefaultTermParser();
            result = parser .parse(
               new StringReader(input), sortType,
               services, services.getNamespaces(),
               MainWindow.getInstance().getMediator().getNotationInfo().getAbbrevMap());
            if (status != null) {
               status.setText("OK");
            }
         }  catch (Exception e) {
            if (status != null) {
               status.setText(e.getMessage());
            }
         }
         return result;
      }
      
      /**
       * @return the ID of the currently selected specification
       */
      private int getSelection() {
         return specSelector.getSelectionIndex();
      }

      /**
       * @param specification - the big tab folder's tab in we want; -1 is current selection
       * @param heap - the small tab folder's tab we want, or the heap index in question; -1 is current selection
       * @param textField - 0 for invariant, 1 for modifies, 2 for variant
       * @return the Text widget containing the specification.
       */
      private Text getTextField(int specification, int heap, int textField) {
         if (specification == -1) {
            specification = getSelection();
         }
         //TabItem tab = editorTab.getItem(specification);
         //ScrolledComposite scrolledComposite = (ScrolledComposite) tab.getControl();
         ScrolledComposite scrolledComposite = (ScrolledComposite) specSwitchComposite.getChildren()[specification];
         Composite txtcontainer = (Composite) scrolledComposite.getContent();
         if (textField == 2) {
            Group vargrp = (Group) txtcontainer.getChildren()[1];
            return (Text) vargrp.getChildren()[0];
         }
         TabFolder tfld = (TabFolder) txtcontainer.getChildren()[0];
         if (heap == -1) {
            heap = tfld.getSelectionIndex();
         }
         Composite modinvcontainer = (Composite) (tfld.getItem(heap).getControl());
         Group modOrVarGrp = (Group) (modinvcontainer.getChildren()[textField]);
         Text wdgt = (Text) modOrVarGrp.getChildren()[0];
         return wdgt;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public IBuiltInRuleApp finish() {
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
         Map<LocationVariable, Term> freeSpec = new LinkedHashMap<LocationVariable, Term>();
         
         //return the new Invariant
         LoopSpecification newInvariant = loopApp.getSpec().configurate(invMap, freeSpec, modMap, infFlowSpecs, variantTerm);
         return loopApp.setLoopInvariant(newInvariant);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
         //remove all listeners
         store.removeSelectionListener(storeListener);
         specSelector.removeSelectionListener(specSelectListener);
         for (int i = 0; i < cListenerParents.size(); i++) {
            cListenerParents.get(i).removeControlListener(cListeners.get(i));
         }
         for (Text p : mListenerParents) {
            p.removeModifyListener(modifyListener);
         }
         for (TabFolder p : heapTabFolders) {
            p.removeSelectionListener(heapTabsListener);
         }
         root.dispose();
      }
   }
}
