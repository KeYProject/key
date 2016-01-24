package org.key_project.key4eclipse.common.ui.wizard.page;

import java.awt.BorderLayout;
import java.awt.Component;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Vector;

import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.border.TitledBorder;

import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.custom.StackLayout;
import org.eclipse.swt.custom.TableEditor;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.swt.widgets.Text;
import org.key_project.key4eclipse.common.ui.util.KeYImages;
import org.key_project.key4eclipse.common.ui.wizard.CompleteAndApplyTacletMatchWizard;
import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.instantiation_model.TacletAssumesModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.SequentViewLogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ModelChangeListener;
import de.uka.ilkd.key.proof.ModelEvent;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.Taclet;
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
   
   private Composite root;

   private Combo specSelector;

   private Composite specSwitchComposite;

   private StackLayout stackLayout;

   private Label validationText;

   private int currentID = 0;
   
   /**
    * Constructor.
    * @param pageName The name of this {@link WizardPage}.
    * @param models The partial models with all different possible instantiations found automatically.
    * @param goal The Goal where to apply.
    */
   public CompleteAndApplyTacletMatchWizardPage(String pageName, TacletInstantiationModel[] models, Goal goal) {
      super(pageName);
      this.models = models;
      this.goal = goal;
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
      root = new SashForm(parent, SWT.HORIZONTAL);
      int defaultSashWidth = 20;
      ((SashForm) root).setSashWidth(defaultSashWidth);
      setControl(root);
      
      //set general layout. Should be easily modifiable.
      SashForm left  = new SashForm(root, SWT.VERTICAL);
      ((SashForm) left).setSashWidth(defaultSashWidth);
      SashForm right = new SashForm(root, SWT.VERTICAL);
      ((SashForm) right).setSashWidth(defaultSashWidth);
      
      //TODO: Are the sashForms clearly visible?
      
      mkTacletView(left);
      mkVariableInstantiationView(right);
      mkProgramVariablesView(left);
      mkValidationView(right);

      specSelector.select(0);
      specSwitchTo(0);
      
      // Set initial page complete state.
      updatePageComplete();
      
      //TODO: Investigate: What do different TacletInstModels we can get have in common?
      //TODO: Validate assumptions: All models share everything *but* tableModel and ifChoiceModel
   }
   
   /**
    * Checks the user input for validity and updates the page complete state.
    */
   protected void updatePageComplete() {
      validationViewUpdate();
   }
   
   private void mkTacletView(Composite parent){
      Taclet taclet = models[0].taclet();
      
      //TODO: Horrible mess beyond this point. Cleanup needed. Are all these calls to various String make thingies really needed?
      StringBackend backend = new StringBackend(68);
      StringBuilder tacletSB = new StringBuilder();

      Writer w = new StringWriter();

      SequentViewLogicPrinter tp = new SequentViewLogicPrinter(
            new ProgramPrinter(w), new NotationInfo(), backend,
            models[0].getServices(), true, MainWindow.getInstance()
                  .getVisibleTermLabels());
      
      tp.printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                  .getShowWholeTaclet(),
            // ProofSettings.DEFAULT_SETTINGS.getViewSettings().getShowWholeTaclet(),
            false);
      tacletSB.append(backend.getString());
      //End of mess, hopefully.
      
      //Make a border and Text field.
      Group statusGrp = new Group(parent, SWT.NONE);
      statusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
      statusGrp.setLayout(new GridLayout(1, false));
      Text tacletText = new Text(statusGrp, SWT.WRAP | SWT.READ_ONLY);
      //show taclet name in group border
      statusGrp.setText("Selected Taclet - " + taclet.name());
      // show taclet
      tacletText.setText(tacletSB.toString());
   }
   
   private void mkVariableInstantiationView(Composite parent){
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
   
   private void mkProgramVariablesView(Composite parent){
      //implementation pretty much completed.
      Group statusGrp = new Group(parent, SWT.NONE);
      statusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
      statusGrp.setLayout(new GridLayout(1, false));
      statusGrp.setText("Sequent program variables");
      Label status = new Label(statusGrp, SWT.WRAP);
      ImmutableList<Named> vars = models[0].programVariables().elements();
      String text;
      if (vars.size() > 0) {
         text = vars.toString();
         text = "";
         for(Named n : vars) {
            text += n.name();
            text += "\n";
         }
      }
      else {
         text = "none";
      }
      status.setText(text);
   }
   
   private void mkValidationView(Composite parent){
      Group statusGrp = new Group(parent, SWT.NONE);
      statusGrp.setLayoutData(new GridData(GridData.FILL_BOTH));
      statusGrp.setLayout(new GridLayout(1, false));
      statusGrp.setText("Input validation result");
      validationText = new Label(statusGrp, SWT.WRAP);
   }
   
   //Not getting called yet, because I'm unsure where.
   private void mkIfSelectionView(Composite parent, TacletInstantiationModel model){
      //Completely untested
      
      if (model.application().taclet().ifSequent().isEmpty()){
         //not going to need a view for that at all.
         return;
      }
      Group ifSelectionViewGrp = new Group(parent, SWT.NONE);
      ifSelectionViewGrp.setText("Assumption instantiation");
      ifSelectionViewGrp.setLayout(new GridLayout(2, false));
      for(int i = 0; i < model.ifChoiceModelCount(); i++) {
         String text = ProofSaver.printAnything(model.ifFma(i), model.proof().getServices());
         Text assumption = new Text(ifSelectionViewGrp, SWT.READ_ONLY);
         assumption.setText(text);
         TacletAssumesModel tam = model.ifChoiceModel(i);
         Combo c = new Combo(ifSelectionViewGrp, SWT.DROP_DOWN);
         Services svc = model.proof().getServices();
         for(int j = 0 ; j < tam.getSize(); j++){
            c.add(tam.getElementAt(j).toString(svc));
         }
         //selection listener for the Combo?
      }
   }
   
   private void specSwitchTo(int id){
      stackLayout.topControl = (Composite) specSwitchComposite.getChildren()[id];
      specSwitchComposite.layout();
      validationViewUpdate();
   }
   
   private TacletInstantiationModel getCurrentModel(){
      return models[currentID ];
   }
   
   private void validationViewUpdate(){
      String status = getCurrentModel().getStatusString();
      validationText.setText(status);
      if (status.equals("Instantiation is OK.")){
         setErrorMessage(null);
         setPageComplete(true);
      } else {
         setErrorMessage("Instantiation has errors. Check the input validation result.");
         setPageComplete(false);
      }
   }
   
   private void mkSpecification(String name, final int id){
      specSelector.add(name);
      TacletInstantiationModel model = models[id];
      Composite specComposite = new Composite(specSwitchComposite, SWT.NONE);
      specComposite.setLayout(new GridLayout(1, false));
      specComposite.setLayout(new FillLayout());
      final Table table = new Table (specComposite, SWT.BORDER | SWT.FULL_SELECTION);
      TableColumn varnames = new TableColumn(table, SWT.NONE);
      TableColumn varspecs = new TableColumn(table, SWT.NONE);
      TableItem item;
      final Vector<TableItem> editableItems = new Vector<TableItem>();
      final Vector<Integer> editableItemOriginalRowID = new Vector<Integer>();
      for(int i = 0; i < model.tableModel().getRowCount(); i++){
         item = new TableItem(table, SWT.NONE);
         String left = model.tableModel().getValueAt(i, 0).toString();
         Object rightSideSpec = model.tableModel().getValueAt(i, 1);
         String right;
         if (rightSideSpec == null) {
            right = "";
         }else{
            right = rightSideSpec.toString();
         }
         item.setText(new String[] {left, right});
         if (rightSideSpec == null) {
            editableItems.add(item);
            editableItemOriginalRowID.add(i);
         }
      }
      varnames.pack();
      varspecs.pack();
      
      //TODO: validate that the code from this snippet
      //http://www.java2s.com/Code/Java/SWT-JFace-Eclipse/editthetextofaSWTtableiteminplace.htm
      //is in line with what we need.
      
      final TableEditor editor = new TableEditor(table);
      // The editor must have the same size as the cell and must
      // not be any smaller than 50 pixels.
      editor.horizontalAlignment = SWT.LEFT;
      editor.grabHorizontal = true;
      editor.minimumWidth = 50;
      // editing the second column
      final int EDITABLECOLUMN = 1;

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
            if (!editableItems.contains(item)){
               return;
            }
            
            final int row = editableItemOriginalRowID.get(editableItems.indexOf(item));
            
            // The control that will be the editor must be a child of the
            // Table
            Text newEditor = new Text(table, SWT.NONE);
            newEditor.setText(item.getText(EDITABLECOLUMN));
            newEditor.addModifyListener(new ModifyListener() {
               public void modifyText(ModifyEvent me) {
                  Text text = (Text) editor.getEditor();
                  editor.getItem().setText(EDITABLECOLUMN, text.getText());
                  //we know, by the above if()s, that we're in column ID 1.
                  //column 0 is not editable.
                  models[id].tableModel().setValueAt(text.getText(), row, 1);
                  validationViewUpdate();
               }
            });
            newEditor.selectAll();
            newEditor.setFocus();
            editor.setEditor(newEditor, item, EDITABLECOLUMN);
         }
      });
   }
}
