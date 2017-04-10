package org.key_project.key4eclipse.common.ui.wizard.page;

import java.io.StringWriter;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.layout.TableColumnLayout;
import org.eclipse.jface.viewers.ColumnWeightData;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.custom.TableEditor;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.*;
import org.key_project.key4eclipse.common.ui.util.KeYImages;
import org.key_project.key4eclipse.common.ui.wizard.CompleteAndApplyTacletMatchWizard;

import de.uka.ilkd.key.control.InstantiationFileHandler;
import de.uka.ilkd.key.control.instantiation_model.TacletAssumesModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.SVInstantiationException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.util.pp.StringBackend;

/**
 * The only {@link WizardPage} shown in a {@link CompleteAndApplyTacletMatchWizard}.
 * @author Martin Hentschel, Viktor Pfanschilling
 */
public class CompleteAndApplyTacletMatchWizardPage extends WizardPage {
   /**
    * The partial models with all different possible instantiations found automatically.
    */
   private final TacletInstantiationModel[] models; 
   
   /**
    * The Goal where to apply.
    */
   private final Goal goal;
   
   /**
    * the root Composite of this page.
    */
   private SashForm root;

   /**
    * The spec selector combo.
    */
   private Combo specSelector;

   /**
    * A Composite with Stack Layout for spec switching.
    */
   private Composite specSwitchComposite;

   /**
    * The stack layout in use by specSwitchComposite.
    */
   private StackLayout stackLayout;

   /**
    * The validationView's Text field.
    */
   private Text validationText;

   private StackLayout assumptionsStackLayout;

   private Group assumptionViewGrp;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param modelsP The partial models with all different possible instantiations found automatically.
    * @param goalP The Goal where to apply.
    */
   public CompleteAndApplyTacletMatchWizardPage(String pageName, TacletInstantiationModel[] modelsP, Goal goalP) {
      super(pageName);
      this.models = modelsP;
      this.goal = goalP;
      setTitle("Choose Taclet Instantiation");
      setDescription("Define instantiations required to apply the taclet.");
      setImageDescriptor(KeYImages.getImageDescriptor(KeYImages.INTERACTIVE_WIZARD));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      // Create root
      Composite parentRoot = new Composite(parent, SWT.NONE);
      parentRoot.setLayout(new GridLayout(1, false));
      setControl(parentRoot);
      //set general layout. Should be easily modifiable.
      root = new SashForm(parentRoot, SWT.HORIZONTAL);
      GridData g = new GridData(GridData.FILL_BOTH);
      g.widthHint = 800;
      g.heightHint = 400;
      root.setLayoutData(g);
      SashForm left  = new SashForm(root, SWT.VERTICAL);
      SashForm right = new SashForm(root, SWT.VERTICAL);
      
      mkTacletView(left);
      mkVariableInstantiationView(right);
      mkProgramVariablesView(left);
      boolean hasAssumptions = mkAssumptionsView(right);
      mkValidationView(right);

      specSelector.select(0);
      specSwitchTo(0);

      root.setWeights(new int[]{30, 70});
      left.setWeights(new int[]{75, 25});
      if (hasAssumptions) {
         right.setWeights(new int[]{50, 25, 25});
      }
      else {
         right.setWeights(new int[]{75, 25});
      }

      // Set initial page complete state.
      updatePageComplete();
   }
   
   /**
    * Checks the user input for validity and updates the page complete state.
    */
   protected void updatePageComplete() {
      validationViewUpdate();
   }
   
   /**
    * Creates the taclet view.
    * @param parent the composite to attach to
    */
   private void mkTacletView(Composite parent) {
      Taclet taclet = models[0].taclet();
      
      //Generate a String that displays the taclet.
      StringBackend backend = new StringBackend(68);
      StringBuilder tacletSB = new StringBuilder();

      SequentViewLogicPrinter tp = new SequentViewLogicPrinter(
         new ProgramPrinter(new StringWriter()), new NotationInfo(), backend,
         models[0].getServices(), true, MainWindow.getInstance().getVisibleTermLabels());
      
      tp.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet(), false);
      tacletSB.append(backend.getString());
      
      //Make a border and Text field.
      Group statusGrp = new Group(parent, SWT.NONE);
      statusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
      statusGrp.setLayout(new GridLayout(1, false));
      Text tacletText = new Text(statusGrp, SWT.WRAP | SWT.V_SCROLL);
      tacletText.setEditable(false);
      tacletText.setLayoutData(new GridData(GridData.FILL_BOTH));
      //show taclet name in group border
      statusGrp.setText("Selected Taclet - " + taclet.name());
      // show taclet
      tacletText.setText(tacletSB.toString());
   }
   
   /**
    * Creates the program variables view.
    * @param parent the composite to attach to
    */
   private void mkProgramVariablesView(Composite parent) {
      //implementation pretty much completed.
      Group statusGrp = new Group(parent, SWT.NONE);
      statusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
      statusGrp.setLayout(new GridLayout(1, false));
      statusGrp.setText("Sequent program variables");
      Text status = new Text(statusGrp, SWT.WRAP | SWT.V_SCROLL);
      status.setLayoutData(new GridData(GridData.FILL_BOTH));
      status.setEditable(false);
      Collection<IProgramVariable> vars = models[0].programVariables().elements();
      String text;
      if (vars.size() > 0) {
         text = vars.toString();
         text = "";
         for (Named n : vars) {
            text += n.name();
            text += "\n";
         }
      } else {
         text = "none";
      }
      status.setText(text);
   }
   
   /**
    * Creates the variable instantiation view.
    * @param parent the composite to attach to
    */
   private void mkVariableInstantiationView(Composite parent) {
      Group programVariablesView = new Group(parent, SWT.NONE);
      programVariablesView.setLayoutData(new GridData(GridData.FILL_BOTH));
      programVariablesView.setLayout(new GridLayout(1, false));
      programVariablesView.setText("Variable instantiations");
      //selector drop down
      specSelector = new Combo(programVariablesView, SWT.DROP_DOWN | SWT.READ_ONLY);
      specSelector.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
      specSelector.addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            specSwitchTo(specSelector.getSelectionIndex());
         }
      });
      
      specSwitchComposite = new Composite(programVariablesView, SWT.NONE);
      specSwitchComposite.setLayoutData(new GridData(GridData.FILL_BOTH));
      stackLayout = new StackLayout();
      specSwitchComposite.setLayout(stackLayout);
      for (int i = 0; i < models.length; i++) {
         mkSpecification("Specification " + i, i);
      }
   }
   
   /**
    * generates a taclet-assumes instantiation view.
    * @param parent the parent composite
    */
   private boolean mkAssumptionsView(Composite parent) {
      if (models[0].application().taclet().ifSequent().isEmpty()) {
         //No Assumptions to instantiate
         return false;
      }
      else {
         //Generate a Group that holds the stack of AssumptionSpec Views for each model.
         assumptionViewGrp = new Group(parent, SWT.NONE);
         assumptionViewGrp.setText("Assumption instantiation");
         assumptionsStackLayout = new StackLayout();
         assumptionViewGrp.setLayout(assumptionsStackLayout);
         for (int i = 0; i < models.length; i++) {
            mkAssumptionsSpec(0);
         }
         return true;
      }
   }
   
   /**
    * Creates the validation view.
    * @param parent the composite to attach to
    */
   private void mkValidationView(Composite parent) {
      Group statusGrp = new Group(parent, SWT.NONE);
      statusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
      statusGrp.setLayout(new GridLayout(1, false));
      statusGrp.setText("Input validation result");
      validationText = new Text(statusGrp, SWT.WRAP | SWT.V_SCROLL);
      validationText.setEditable(false);
      validationText.setLayoutData(new GridData(GridData.FILL_BOTH));
   }
   
   /**
    * Switches to a different spec.
    * @param id The ID of the spec in models
    */
   private void specSwitchTo(int id) {
      stackLayout.topControl = specSwitchComposite.getChildren()[id];
      specSwitchComposite.layout();
      if (assumptionsStackLayout != null && assumptionViewGrp != null) {
         assumptionsStackLayout.topControl = assumptionViewGrp.getChildren()[id];
         assumptionViewGrp.layout();
      }
      validationViewUpdate();
   }
   
   /**
    * @return The model currently selected.
    */
   private TacletInstantiationModel getCurrentModel() {
      return models[specSelector.getSelectionIndex()];
   }
   
   /**
    * Updates the validation View.
    */
   private void validationViewUpdate() {
      String status = getCurrentModel().getStatusString();

      validationText.setText(status);
      if (status.equals("Instantiation is OK.")) {
         setErrorMessage(null);
         setPageComplete(true);
      } else {
         setErrorMessage("Instantiation has errors. Check the input validation result.");
         setPageComplete(false);
      }
   }
   
   /**
    * Creates a new specification.
    * @param name The alias in the DropDown Combo
    * @param id The ID in models
    */
   private void mkSpecification(String name, final int id) {
      specSelector.add(name);
      TacletInstantiationModel model = models[id];
      Composite specComposite = new Composite(specSwitchComposite, SWT.NONE);
      TableColumnLayout tableLayout = new TableColumnLayout();
      specComposite.setLayout(tableLayout);
      final Table table = new Table(specComposite, SWT.BORDER | SWT.FULL_SELECTION);
      table.setHeaderVisible(true);
      table.setLinesVisible(true);
      TableColumn varnames = new TableColumn(table, SWT.NONE);
      varnames.setText("formula");
      TableColumn varspecs = new TableColumn(table, SWT.NONE);
      varspecs.setText("instantiation");
      tableLayout.setColumnData(varnames, new ColumnWeightData(20));
      tableLayout.setColumnData(varspecs, new ColumnWeightData(80));
      final List<TableItem> editableItems = new LinkedList<TableItem>();
      final List<Integer> editableItemOriginalRowID = new LinkedList<Integer>();
      for (int i = 0; i < model.tableModel().getRowCount(); i++) {
         TableItem item = new TableItem(table, SWT.NONE);
         String left = model.tableModel().getValueAt(i, 0).toString();
         Object rightSideSpec = model.tableModel().getValueAt(i, 1);
         String right;
         if (rightSideSpec == null) {
            right = "enter specification here";
         } else {
            right = rightSideSpec.toString();
         }
         item.setText(new String[] {left, right});
         if (model.tableModel().isCellEditable(i, 1)) {
            editableItems.add(item);
            editableItemOriginalRowID.add(i);
         }
      }
      
      final TableEditor editor = new TableEditor(table);
      editor.horizontalAlignment = SWT.RIGHT;
      editor.grabHorizontal = true;

      table.addSelectionListener(new SelectionAdapter() {
         public void widgetSelected(SelectionEvent e) {
            // Clean up any previous editor control
            Control oldEditor = editor.getEditor();
            if (oldEditor != null) {
               oldEditor.dispose();
            }

            // Identify the selected row
            TableItem item = (TableItem) e.item;
            if (item == null) {
               return;
            }
            
            //check if row is editable.
            if (!editableItems.contains(item)) {
               return;
            }
            //get row index
            final int row = editableItemOriginalRowID.get(editableItems.indexOf(item));
            
            //Add a editor
            Text newEditor = new Text(table, SWT.NONE);
            newEditor.setText(item.getText(1));
            newEditor.addModifyListener(new ModifyListener() {
               public void modifyText(ModifyEvent me) {
                  Text text = (Text) editor.getEditor();
                  editor.getItem().setText(1, text.getText());
                  //we know, by the above if()s, that we're in column ID 1.
                  //column 0 is not editable.
                  models[id].tableModel().setValueAt(text.getText(), row, 1);
                  validationViewUpdate();
               }
            });
            newEditor.selectAll();
            newEditor.setFocus();
            editor.setEditor(newEditor, item, 1);
         }
      });
   }
   
   /**
    * Constructs a assumptions specification specification composite - one combo per assumption.
    * @param id the id of the model to use.
    */
   private void mkAssumptionsSpec(final int id) {
      final TacletInstantiationModel model = models[id];
      Composite ifSelectionViewComposite = new Composite(assumptionViewGrp, SWT.NONE);
      ifSelectionViewComposite.setLayout(new GridLayout(2, true));
      final Services svc = model.proof().getServices();
      
      //For each required Assumption:
      for (int i = 0; i < model.ifChoiceModelCount(); i++) {
         //create a line in the assumptions field:
         //assumption text
         String text = ProofSaver.printAnything(model.ifFma(i), model.proof().getServices());
         Text assumption = new Text(ifSelectionViewComposite, SWT.READ_ONLY);
         assumption.setText(text);
         final TacletAssumesModel tam = model.ifChoiceModel(i);
         //combo box
         final Combo c = new Combo(ifSelectionViewComposite, SWT.DROP_DOWN);
         c.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
         final int ifChoiceModelID = i;
         int manualInputIDTemp = -1;
         //combo box contents:
         for (int j = 0; j < tam.getSize(); j++) {
            String ifSelection = tam.getElementAt(j).toString(svc);
            if (!ifSelection.equals("Manual Input")) {
               c.add(ifSelection);
            } else {
               //Do not use Manual Input items, instead keep their position for later use.
               manualInputIDTemp = j;
            }
            
         }
         final int manualInputID = manualInputIDTemp;
         c.addSelectionListener(new SelectionAdapter() {
            @Override
            public void widgetSelected(SelectionEvent e) {
               //feed back to model: assumption selection changed.
               tam.setSelectedItem(tam.getElementAt(c.getSelectionIndex()));
            }
         });
         c.addModifyListener(new ModifyListener() {
            public void modifyText(ModifyEvent e) {
               //defaults to -1 if c's text cannot be found in the model.
               //That is, if the user entered something.
               int index = c.getSelectionIndex();
               
               //set the input we received.
               //No ill effects if the selected Item is not Manual Input.
               model.setManualInput(ifChoiceModelID, c.getText());
               
               if (index == -1) {
                  //Manual Input
                  tam.setSelectedItem(tam.getElementAt(manualInputID));
               } else {
                  //Existing Selection
                  tam.setSelectedItem(tam.getElementAt(index));
               }
               validationViewUpdate();
               
            }
         });
      }
   }
   
   /**
    * Stores the information and applies a freshly created taclet application.
    * @throws SVInstantiationException Occurred Exception.
    */
   public void finish() throws SVInstantiationException {
      validationViewUpdate();
      TacletApp app = getCurrentModel().createTacletApp();
      if (app == null) {
         return;
      }
      goal.apply(app);
      InstantiationFileHandler.saveListFor(getCurrentModel());
   }
}
