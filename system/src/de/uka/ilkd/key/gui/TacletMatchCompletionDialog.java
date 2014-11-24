// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.Transferable;
import java.awt.datatransfer.UnsupportedFlavorException;
import java.awt.dnd.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.*;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

import javax.swing.*;
import javax.swing.border.EmptyBorder;
import javax.swing.border.TitledBorder;
import javax.swing.event.ChangeEvent;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableCellRenderer;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.configuration.PathConfig;
import de.uka.ilkd.key.gui.utilities.BracketMatchingTextArea;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExceptionHandlerException;

public class TacletMatchCompletionDialog extends ApplyTacletDialog {

    /**
     * 
     */
    private static final long serialVersionUID = 5124050224007103908L;

    // the table showing the instantiations
    private DataTable[] dataTable;

    // the current chosen model
    private int current = 0;

    // the gui component used to display the different instantiation
    // alternatives
    private JTabbedPane alternatives;
    
    /** the goal the application of the rule has to be performed */
    private Goal goal;

    private JScrollPane tablePane;

    private MainWindow mainWindow;
 
    public TacletMatchCompletionDialog(MainWindow parent, ApplyTacletDialogModel[] model,
				       Goal goal, KeYMediator mediator) { 
	super(parent, model, mediator);
	setName("tacletMatchDlg");
	this.mainWindow = parent;
	this.goal    = goal;
	this.current = 0;
	dataTable = new DataTable[model.length];

        for (ApplyTacletDialogModel aModel : model) {
            aModel.prepareUnmatchedInstantiation();
        }
        
        setStatus();
	
        // layout dialog
	layoutDialog();
        pack();

        // reload previously set GUI
        mainWindow.loadPreferences(this);

	setVisible(true);
    }
    
       
    
    public static ApplyTacletDialogModel[] completeAndApplyApp(java.util.List<TacletApp> apps, Goal goal,
            KeYMediator medi) {
        ApplyTacletDialogModel[] origInstModels = new ApplyTacletDialogModel[apps.size()];
        LinkedList<ApplyTacletDialogModel> recentInstModels = new LinkedList<ApplyTacletDialogModel>();

        int appCounter = 0;
        for (final TacletApp tA : apps) {            
            origInstModels[appCounter] = createModel(tA, goal, medi);

            if (InstantiationFileHandler.hasInstantiationListsFor(tA
                    .taclet())) {
                for (final List<String> instantiations : 
                    InstantiationFileHandler.getInstantiationListsFor(tA.taclet())) {
                    int start = tA.instantiations().size();

                    if (origInstModels[appCounter].tableModel().getRowCount() - start ==
                            instantiations.size()) {
                        ApplyTacletDialogModel m = createModel(tA,
                                goal, medi);
                        recentInstModels.add(m);
                        for (final String inst : instantiations) {
                            m.tableModel().setValueAt(inst, start++, 1);
                        }
                    }
                }
            }
            appCounter++;
        }

        ApplyTacletDialogModel[] models = new ApplyTacletDialogModel[
                origInstModels.length + recentInstModels.size()];
        int i;
        for (i = 0; i < origInstModels.length; i++) {
            models[i] = origInstModels[i];
        }

        for (final ApplyTacletDialogModel model : recentInstModels) {
            models[i++] = model;
        }

        return models;
    }

    public static ApplyTacletDialogModel createModel(TacletApp app, Goal goal, 
                                                     KeYMediator medi) {
       final Namespace progVars = new Namespace(); 
       progVars.add(goal.getGlobalProgVars());
       
       return new ApplyTacletDialogModel(
            app, goal.sequent(), medi.getServices(),
	    new NamespaceSet(medi.var_ns(),
			     medi.func_ns(),
			     medi.sort_ns(),
			     medi.heur_ns(),
			     medi.choice_ns(),
			     progVars),
	    medi.getNotationInfo().getAbbrevMap(),
	    goal);
    }
    

    public void setStatus() {
        setStatus(model[current].getStatusString());
    }

    
    private void layoutDialog() {

	JPanel tacletPanel=createTacletPanel();
	JPanel downPanel=new JPanel();
	downPanel.setLayout(new BoxLayout(downPanel, BoxLayout.Y_AXIS));
	downPanel.add(createInfoPanel());
	downPanel.add(createStatusPanel());
	downPanel.add(createButtonPanel(new ButtonListener()));
	
	JSplitPane splitPaneBot = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
	        tacletPanel, downPanel);
	// work around bug in com.togethersoft.util.ui.plaf.metal.OIMetalSplitPaneUI
//	{
//	    public void setUI(javax.swing.plaf.SplitPaneUI ui) {
//	        try{ super.setUI(ui); } catch(NullPointerException e)
//	        { Debug.out("Exception thrown by class TacletMatchCompletionDialog at setUI");}
//	    }
//	};
	splitPaneBot.setResizeWeight(1);
	splitPaneBot.setName("tacletMatchDlg.splitBottom");

	JSplitPane splitPane = new JSplitPane(JSplitPane.VERTICAL_SPLIT,
                                   createTacletDisplay(), splitPaneBot);
//	{
//
//	    public void setUI(javax.swing.plaf.SplitPaneUI ui) {
//	        try{ super.setUI(ui); } catch(NullPointerException e) 
//	        {Debug.out("Exception thrown by class TacletMatchCompletionDialog at setUI"); }
//	    }
//	}; 
        // work around bug in com.togethersoft.util.ui.plaf.metal.OIMetalSplitPaneUI
	splitPane.setName("tacletMatchDlg.split");
	
	getContentPane().add(splitPane);
	// add button listener
	updateDataModel();
    }
        
    private JPanel createTacletPanel() {
	// the tabbedPane contains different possible instantiations of 
	// the applied Taclet
	JPanel panel = new JPanel(new GridLayout(1,1));	
	panel.setBorder(new TitledBorder("Variable Instantiations"));
	
	alternatives = new JTabbedPane();	
	// some layout stuff 
	EmptyBorder indents = new EmptyBorder(5,5,5,5);	
	
	for (int i = 0; i < model.length; i++) {
	    JPanel tabContent = new JPanel();
	    tabContent.setLayout(new BoxLayout(tabContent, BoxLayout.Y_AXIS));

	    JPanel instPanel = createInstantiationDisplay(i);
	    instPanel.setBorder(indents);
	    tabContent.add(instPanel);

	    if (!model[i].application().taclet().
		ifSequent().isEmpty()) {

		TacletIfSelectionDialog ifSelection = 
		    new TacletIfSelectionDialog(model[i], this);		
		dataTable[i].setIfSelectionPanel(ifSelection);
		tabContent.add(ifSelection);
	    } 
	    alternatives.addTab("Alt "+i, null, tabContent, 
			  "Instantiations Alternatives");
	}

	panel.add(alternatives);
	return panel;
    }

    /** returns the current selected model 
     * @return the current selected model 
     */
    protected int current() {
	return alternatives.getSelectedIndex();
    }

    protected void pushAllInputToModel() {
	pushAllInputToModel(current());
    }

    protected void pushAllInputToModel(int i) {
	if (dataTable[i].hasIfSelectionPanel()) {
	    dataTable[i].getIfSelectionPanel().pushAllInputToModel();
	}
	if (dataTable[i].isEditing()) {
	    dataTable[i].getCellEditor().stopCellEditing();
	}
    }

    private JPanel createInstantiationDisplay(int i) {
	JPanel panel = new JPanel(new BorderLayout());
	// show instantiation
	dataTable[i] = new DataTable(this, i);
        dataTable[i].setRowHeight(48);
        tablePane = new JScrollPane(dataTable[i]);
        adaptSizes(dataTable[i]);       
	panel.add(tablePane, 
		  BorderLayout.CENTER);
	return panel;
    }

    private void adaptSizes(DataTable dt) {
	int tableSize_x = dt.getTotalColumnWidth();
	int visible_rows = dt.getRowCount() > 8 ? 8 : 
	    dt.getRowCount();
	int tableSize_y = (visible_rows + 1) * 48;  
	Dimension tableDim = new Dimension(tableSize_x, tableSize_y);
	// bugfix. march-09 m.u.:
	// removed calls to tablePane.setMinimumSize and setMaximumSize
	// because they prevented the scrollbar from appearing (esp. in
	// low screen resolution)
 	tablePane.setPreferredSize(tableDim);
	validate();
    }

    private void setColumnName(int model, int col, String name) {
	dataTable[model].
	    getColumn(dataTable[model].getColumnName(col)).
	    setHeaderValue(name);
    }

    /** shows next instantiation suggestion */
    private void updateDataModel() {	
	for (int i = 0; i < model.length; i++) {
	    if (model[i] != null) {
		dataTable[i].setModel(model[i].tableModel());		
		//sets column names
		setColumnName(i, 0, "Variable");
		setColumnName(i, 1, "Instantiation");	    
	    }
	}
    }


    /**
     * save the preferences of this window prior to closing it.
     */
    @Override 
    protected void closeDlg() {
        if(mainWindow != null)
            mainWindow.savePreferences(this);
        super.closeDlg();
    }


    class ButtonListener implements ActionListener {
       
       
       public ButtonListener() {         
       }
     

	private void errorPositionKnown( String errorMessage, 
					 int    row,
					 int    col, 
					 boolean inIfSequent) {

	    if ( inIfSequent ) {
		dataTable[current()].
		    getIfSelectionPanel().requestFocusAt(row, col);
	    } else {
		// select table cell where the error occured
		//ALL THIS DOES NOT REALLY WORK!!! BUT WHY???
		final int tableCol = 1;
		dataTable[current()].editCellAt(row, tableCol);
		dataTable[current()].setEditingRow(row);
		dataTable[current()].setEditingColumn(tableCol);

		PositionSettable ed = (PositionSettable)dataTable[current()]
		    .getCellEditor(row, tableCol);

		try {
		    
		    ed.setCaretPosition( col - 1 );

		} catch (IllegalArgumentException iae) {
		    Debug.out("tacletmatchcompletiondialog:: something is " + 
				       "wrong with the caret position calculation.");

		}
		ed.setVisible(true);		   		    
		ed.validate();
		ed.requestFocus();
	    }
	}
	
	
	public void actionPerformed(ActionEvent e) {
	    if (e.getSource() == cancelButton) {
		closeDialog();
	    } else if (e.getSource() == applyButton) {		      
		try {
		    try {
			pushAllInputToModel();
			TacletApp app = model[current()].createTacletApp();
			if (app == null) {
			    JOptionPane.showMessageDialog
				(TacletMatchCompletionDialog.this,
				 "Could not apply rule",
				 "Rule Application Failure",
				 JOptionPane.ERROR_MESSAGE);   
			    return ;
			}
			mediator().applyInteractive(app, goal);
		    } catch (ExceptionHandlerException ex){
			throw ex;
		    } catch(Exception ex) {			
			(mediator().getExceptionHandler()).reportException(ex); 
		    }
		}  catch (ExceptionHandlerException ex) { 
		    Exception exc = (Exception) ((mediator().getExceptionHandler()).getExceptions()).get(0);
		    if (exc instanceof SVInstantiationExceptionWithPosition) {
                        errorPositionKnown(exc.getMessage(),
                                ((SVInstantiationExceptionWithPosition) exc).getRow(),
                                ((SVInstantiationExceptionWithPosition) exc).getColumn(),
                                ((SVInstantiationExceptionWithPosition) exc).inIfSequent());
		    }
		    ExceptionDialog.showDialog(TacletMatchCompletionDialog.this, 
		            mediator().getExceptionHandler().getExceptions());
		    mediator().getExceptionHandler().clear();
		    return ;
		} 
		InstantiationFileHandler.saveListFor(model[current()]);
		closeDialog();
	    }
	}

	private void closeDialog() {
	    closeDlg();
	    setVisible(false);
	    dispose();
	}

    }
    
    private static class DataTable extends JTable 
	implements ModelChangeListener {

	/**
         * 
         */
        private static final long serialVersionUID = 5988602390976062610L;
        //JTextArea inputArea=new JTextArea("Nothing",3,16);
        JTextArea inputArea=new BracketMatchingTextArea("Nothing",3,16);
	final InputEditor iEditor = new InputEditor(inputArea);
	final InputCellRenderer iRenderer = new InputCellRenderer();
	
	/** the number of the model the data table belongs to */
	private int modelNr;
	/** the enclosing dialog */	
	private TacletMatchCompletionDialog owner;
	/** the TacletIfSelectionPanel that shows the different possible
	 * instantiations of the if-sequent or a manual entered
	 * instantiation. The value is null if and only if
	 * the taclet has no if-sequent
	 */
	private TacletIfSelectionDialog ifSelectionPanel;

	private DataTable(TacletMatchCompletionDialog owner,
			  int modelNr) {

	    super(owner.model[modelNr].tableModel());
	    this.modelNr = modelNr;
	    this.owner = owner;
	    owner.model[modelNr].addModelChangeListener(this);
	    setUpEditor();

	    // And now the Drag'n'drop stuff ...
	    DropTarget aDropTarget = 
		new DropTarget(this, new DropTargetListener() {
			public void dragEnter (DropTargetDragEvent event) {}
	
			public void dragExit (DropTargetEvent event) {}
			     
			public void dragOver (DropTargetDragEvent event) {}
			    
			public void drop (DropTargetDropEvent event) {
			    String droppedString;
				 
			    Point dropLocation = event.getLocation();
			    int row = DataTable.this.rowAtPoint( dropLocation );
			    int column = DataTable.this.columnAtPoint( dropLocation );

			    if ((row != -1) && (column == 1)){
				// The point lies within the table and within the instantiation
				// column ...

				try {
				    Transferable transferable = event.getTransferable();
						   
				    // we accept only Strings      
				    if (transferable.isDataFlavorSupported (DataFlavor.stringFlavor)){
						       
					event.acceptDrop(DnDConstants.ACTION_MOVE);
					droppedString = (String)transferable.getTransferData ( DataFlavor.stringFlavor);
					// now set the new entry in the table ...

					if(droppedString != null){
							   
					    DataTable.this.setValueAt(droppedString, row, column);
					    DataTable.this.repaint();
					}
					event.getDropTargetContext().dropComplete(true);
				    } 
				    else{
					event.rejectDrop();
				    }
				}
				catch (IOException exception) {
				    exception.printStackTrace();
				    event.rejectDrop();
				} 
				catch (UnsupportedFlavorException ufException ) {
				    ufException.printStackTrace();						   
				    event.rejectDrop();
				}
			    } else {
				event.rejectDrop();
			    }
			}

			public void dropActionChanged(DropTargetDragEvent dtde) {}
		    }); 

        
	    this.setDropTarget(aDropTarget);

	} // end constructor
        
        
	/** Provide sane single-click editing in table */
	public javax.swing.table.TableCellEditor getCellEditor(int row, int col) { 
		return iEditor;
         }

	
        public TableCellRenderer getCellRenderer(int row, int col) {	
		return iRenderer;
	}

	public Object getValueAt(int x, int y) {
	    Object value=super.getValueAt(x, y);
	    if (value==null) return "";
	    return value;
	}

	private void setUpEditor() {
	    setDefaultEditor(String.class, iEditor);
							   
	}

	/** sets the if selection panel */
	private void setIfSelectionPanel
	    (TacletIfSelectionDialog ifSelectionPanel) {
	    this.ifSelectionPanel = ifSelectionPanel;	    
	}

	/** returns the if selection panel
	 * @return the if selection panel, null if not available
	 */
	private TacletIfSelectionDialog getIfSelectionPanel() {
	    return ifSelectionPanel;	    
	}

	/** returns true the model has a non empty if sequent and
	 * the ifSelectionPanel has been created and set. So that the
	 * method getIfSelectionPanel will not return null
	 * @return true iff getIfSelectionPanel does not return null
	 */
	private boolean hasIfSelectionPanel() {
	    return getIfSelectionPanel() != null;	    
	}

	public void modelChanged(ModelEvent me) {
	    if (me.getSource() instanceof ApplyTacletDialogModel) {
		setModel(((ApplyTacletDialogModel)me.getSource()).tableModel());
		repaint();
	    }
	}

	public int getTotalColumnWidth() {
	    return getColumnModel().getTotalColumnWidth();
	}

// 	public int getRowHeight(int row) {
// 	    if (rowHeights==null) return 48;
// 	    return rowHeights[row]*16;
// 	}
		
	public void editingStopped(ChangeEvent e) {	    
	    if (modelNr == owner.current()) {
		super.editingStopped(e);
		owner.pushAllInputToModel(modelNr);
		if (owner.checkAfterEachInput()) {
		    owner.setStatus(owner.model[modelNr].
				getStatusString());
		}
	    }
	}	

	class InputEditor extends DefaultCellEditor implements PositionSettable{

	    /**
         * 
         */
        private static final long serialVersionUID = 1547755822847646366L;
        JPanel editPanel;
	    JTextArea textarea;

	    public InputEditor(JTextArea ta) {
                super(new JCheckBox()); //Unfortunately, the constructor
                                        //expects a check box, combo box,
                                        //or text field.
		textarea=ta;
		editPanel = new JPanel();
		editPanel.setLayout(new BoxLayout(editPanel, BoxLayout.X_AXIS));
		editPanel.add(new JScrollPane(textarea,
					      ScrollPaneConstants
					      .VERTICAL_SCROLLBAR_AS_NEEDED,
					      ScrollPaneConstants
					      .HORIZONTAL_SCROLLBAR_AS_NEEDED));
		JPanel buttonPanel=new JPanel(new BorderLayout());
		Insets zeroIn=new Insets(0,0,0,0);
		JButton less=new JButton("-");
		less.setMargin(zeroIn);
		JButton more=new JButton("+");
		more.setMargin(zeroIn);
 		Dimension small=new Dimension(20,9999);
 		buttonPanel.setMaximumSize(small);
 		buttonPanel.setPreferredSize(small);
 		Dimension smallSq=new Dimension(20,20);
 		less.setMaximumSize(smallSq);
 		less.setMinimumSize(smallSq);
 		less.setPreferredSize(smallSq);
 		more.setMaximumSize(smallSq);
 		more.setMinimumSize(smallSq);
 		more.setPreferredSize(smallSq);
		less.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {
			    if (textarea.getRows()>3) {
		 		textarea.setRows(textarea.getRows()-1);
				setRowHeight(getSelectedRow(), 
					     getRowHeight(getSelectedRow())-16);
				setValueAt(textarea.getText(), getSelectedRow(), 
					   getSelectedColumn());
			    }
			}
		    }); 
		more.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent e) {		    
			    textarea.setRows(textarea.getRows()+1);
			    setRowHeight(getSelectedRow(), 
					 getRowHeight(getSelectedRow())+16);
			    setValueAt(textarea.getText(), getSelectedRow(), 
				       getSelectedColumn());
			}
		    }); 
		buttonPanel.add(less, BorderLayout.NORTH);
		buttonPanel.add(more, BorderLayout.SOUTH);
		editPanel.add(buttonPanel);
		editorComponent=editPanel;
		setClickCountToStart(1);
		DropTarget aDropTarget = 
		    new DropTarget(ta, new DropTargetListener() {
			    public void dragEnter (DropTargetDragEvent event) {}
	
			    public void dragExit (DropTargetEvent event) {}
			     
			    public void dragOver (DropTargetDragEvent event) {}
			    
			    public void drop (DropTargetDropEvent event) {
				Transferable transferable = event.getTransferable();
				if (transferable.isDataFlavorSupported 
				    (DataFlavor.stringFlavor)){	  
				    event.acceptDrop(DnDConstants.ACTION_MOVE);
				    try {
					String droppedString = (String)transferable
					    .getTransferData 
					    (DataFlavor.stringFlavor);
					int pos=textarea.viewToModel
					    (event.getLocation());
					textarea.insert(droppedString, pos);
					event.getDropTargetContext()
					    .dropComplete(true);
				    } catch (UnsupportedFlavorException e) {
					e.printStackTrace();
					event.rejectDrop();
				    } catch (java.io.IOException e) {
					e.printStackTrace();
					event.rejectDrop();
				    }
				} else {
				    event.rejectDrop();
				}
								
			    }
			    public void dropActionChanged(DropTargetDragEvent dtde) {}
			});        
		ta.setDropTarget(aDropTarget);
	    }

	    protected void fireEditingStopped() {
		super.fireEditingStopped();
	    }

	    public Object getCellEditorValue() {
		return textarea.getText();
	    }

	    public void setCaretPosition(int i) {
		textarea.setCaretPosition(i);
	    }

	    public void setVisible(boolean b) {
		textarea.setVisible(b);
	    }
	    public void validate() {
		textarea.validate();
	    }
	    public void requestFocus(){
		textarea.requestFocus();
	    }


	    public Component getTableCellEditorComponent(JTable table, 
							 Object value,
							 boolean isSelected,
							 int row,
							 int column) {
		if (value==null) value="";
		textarea.setText(value.toString());
		textarea.setRows(getRowHeight(row)/16);
		return editorComponent;
	    }

	}

	class InputCellRenderer extends DefaultTableCellRenderer {
	    
	    /**
         * 
         */
        private static final long serialVersionUID = -7270236368657110379L;
        JTextArea ta=new JTextArea("nothing");

	    public Component getTableCellRendererComponent
		(JTable table, Object obj, 
		 boolean isSelected, boolean hasFocus,
		 int row, int column) {
		if (obj==null) obj="";	
		ta.setRows(getRowHeight(row)/16);
		ta.setText(obj.toString());
		if (table.isCellEditable(row,1)) { 
		    //	    ta.setBackground(Color.yellow.brighter());
		    ta.setForeground(Color.black);
		} else {
		    ta.setBackground(Color.white);
		    ta.setForeground(Color.gray);
		}
		return ta;
	    }
	}
    }

    interface PositionSettable {
	void setCaretPosition(int i);
	void setVisible(boolean b);
	void validate();
	void requestFocus();
    }

    private static class InstantiationFileHandler {
        private static final String INSTANTIATION_DIR = 
            PathConfig.getKeyConfigDir() + File.separator + "instantiations";

        private static final String SEPARATOR1 = "<<<<<<";

        private static final String SEPARATOR2 = ">>>>>>";

        private static final String LINE_END = System
                .getProperty("line.separator");

        private static final int SAVE_COUNT = 5;

        private static HashMap<String, List<List<String>>> hm;

        private static boolean hasInstantiationListsFor(Taclet taclet) {
            if (hm == null) {
                createHashMap();
            }
            return hm.containsKey(taclet.name().toString());
        }

        private static java.util.List<List<String>> getInstantiationListsFor(Taclet taclet) {
            if (hasInstantiationListsFor(taclet)) {
                if (hm.get(taclet.name().toString()) == null) {
                    createListFor(taclet);
                }
                return hm.get(taclet.name().toString());
            }
            return null;
        }

        private static void createHashMap() {
            File dir = new File(INSTANTIATION_DIR);
            if (!dir.exists()) {
                dir.mkdirs();
            }
            String[] instFiles = dir.list();
            if (instFiles == null) {
                hm = new LinkedHashMap<String, List<List<String>>>(0);
            } else {
                // Avoid resizing of HashMap
                hm = new LinkedHashMap<String, List<List<String>>>(instFiles.length + 1, 1);
                for (String instFile : instFiles) {
                    hm.put(instFile, null);
                }
            }
        }

        private static void createListFor(Taclet taclet) {
            java.util.List<List<String>> instList = new LinkedList<List<String>>();
            java.util.List<String> instantiations = new LinkedList<String>();
            BufferedReader br = null;
            try {
                br = new BufferedReader(new FileReader(
                        INSTANTIATION_DIR + File.separator
                                + taclet.name().toString()));
                String line = br.readLine();
                StringBuffer sb = new StringBuffer();
                while (line != null) {
                    if (line.equals(SEPARATOR1)) {
                        if (sb.length() > 0) {
                            instantiations.add(sb.toString());
                        }
                        sb = new StringBuffer();
                        if (instantiations.size() > 0) {
                            instList.add(instantiations);
                        }
                        instantiations = new LinkedList<String>();
                    } else if (line.equals(SEPARATOR2)) {
                        if (sb.length() > 0) {
                            instantiations.add(sb.toString());
                        }
                        sb = new StringBuffer();
                    } else {
                        if (sb.length() > 0) {
                            sb.append(LINE_END);
                        }
                        sb.append(line);
                    }
                    line = br.readLine();
                }
                if (sb.length() > 0) {
                    instantiations.add(sb.toString());
                }
            } catch (IOException e) {
            } finally {
                if (br != null) {
                    try {
	                br.close();
                    } catch (IOException e) {
                    }        	
                }
            }
            if (instantiations.size() > 0) {
                instList.add(instantiations);
            }
            hm.put(taclet.name().toString(), instList);
        }

        private static void saveListFor(ApplyTacletDialogModel model) {
            Taclet taclet = model.taclet();
            TacletInstantiationsTableModel tableModel = model.tableModel();
            int start = model.tacletApp().instantiations().size();
            java.util.List<List<String>> instList = getInstantiationListsFor(taclet);
            BufferedWriter bw = null;
            try {
                bw = new BufferedWriter(new FileWriter(
                        INSTANTIATION_DIR + File.separator
                                + taclet.name().toString()));
                StringBuffer sb = new StringBuffer();
                for (int i = start; i < tableModel.getRowCount(); i++) {
                    if (i > start) {
                        sb.append(SEPARATOR2).append(LINE_END);
                    }
                    sb.append(tableModel.getValueAt(i, 1)).append(LINE_END);
                }
                String newInst = sb.toString();
                bw.write(newInst);
                if (instList != null) {
                    final ListIterator<List<String>> instListIt = instList.listIterator();
                    int count = 1;
                    while (instListIt.hasNext() && count < SAVE_COUNT) {
                        final ListIterator<String> instIt = instListIt.next().listIterator();
                        sb = new StringBuffer();
                        for (int i = 0; instIt.hasNext(); i++) {
                            if (i > 0) {
                                sb.append(SEPARATOR2).append(LINE_END);
                            }
                            sb.append(instIt.next()).append(LINE_END);
                        }
                        String oldInst = sb.toString();
                        if (!oldInst.equals(newInst)) {
                            bw.write(SEPARATOR1 + LINE_END + oldInst);
                            count++;
                        }
                    }
                }
            } catch (IOException e) {
            } finally {
                if (bw != null) {
                    try {
	                bw.close();
                    } catch (IOException e) {
                    }        	
                }
            }
            hm.put(taclet.name().toString(), null);
        }

    }

}