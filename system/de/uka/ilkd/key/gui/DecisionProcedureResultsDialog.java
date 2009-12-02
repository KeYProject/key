package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.table.DefaultTableModel;

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofEvent;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.smt.CVC3Solver;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.smt.SMTRuleMulti;
import de.uka.ilkd.key.smt.SMTSolverResult;
import de.uka.ilkd.key.smt.SimplifySolver;
import de.uka.ilkd.key.smt.YicesSolver;
import de.uka.ilkd.key.smt.Z3Solver;
import de.uka.ilkd.key.util.Debug;

public class DecisionProcedureResultsDialog extends JFrame {

    private final KeYMediator mediator;
    private JTextArea textArea;
    private DefaultTableModel tableModel;
    private JTable table; 
    /**The current proof object in focus */
    private Proof proof;
    private final SMTSolverProofListener listener;
    private static DecisionProcedureResultsDialog instance;
    public final static Object[] columnNames = {"Node", CVC3Solver.name, YicesSolver.name, Z3Solver.name, SimplifySolver.name};
    
    /**The window is set visible by the ProofTree event smtDataUpdate */
    protected DecisionProcedureResultsDialog(KeYMediator medi){
	//super(mediator.mainFrame(), "SMT Solver Progress and Results");
	super("SMT Solver Progress and Results");
	this.mediator = medi;
	listener = new SMTSolverProofListener();
	//mediator.addRuleAppListener(listener);
	mediator.addKeYSelectionListener(listener);
	layoutWindow();
	table.getSelectionModel().addListSelectionListener(new ListSelectionListener(){

	    public void valueChanged(ListSelectionEvent arg0) {
		assert arg0.getSource()==table;
		assert table.getModel()==tableModel;
		int idx = table.getSelectedRow();
		
		if(idx < tableModel.getRowCount()){
		    if(idx>=0){
        		NodeWrap nw = (NodeWrap)tableModel.getValueAt(idx, 0);
        		Node n = nw.n;
        		mediator.getSelectionModel().setSelectedNode(n);
		    }
		    updateTextArea(idx);//-1 is accepted
		}
            }
	});
	
	//this.setVisible(true);
    }
    
    /**Creates a new instance or returns an existing instance if one already exists.
     * Does not create a window if medi is null.
     * The window is set visible by an smtDataUpdate event.
     * This method registers a KeYSelectionListener at the mediator and a
     * ProofTreeListener when a proof is selected. */
    public static DecisionProcedureResultsDialog getInstance(KeYMediator medi){
	if(instance==null){
	    if(medi==null){
		return null;
	    }
	    instance = new DecisionProcedureResultsDialog(medi);
	}
	return instance;
    }
    
    private void layoutWindow(){
	
	//Todo the columns could be extended dynamically instead of this static initialization
	
	tableModel = new DefaultTableModel(columnNames,0);
	table = new JTable(tableModel);
	table.setToolTipText("<html>Solver outputs are TRUE, UNKNOWN, FALSIFIABLE.<br> " +
			"Note that weakening is performed, when the node contains<br>" +
			"formulas or terms not directly translatable to FOL, such as<br>" +
			"dynamic logic formulas. In this case the result FALSIFIABLE is <br>" +
			"not sound and you should apply KeY rules to eliminate such formulas</html>");
	
	
	JScrollPane tableScrollPane = new JScrollPane(table);
	tableScrollPane.setPreferredSize(new Dimension(300, 350));
	//tableScrollPane.setMinimumSize(minimumSize);
	tableScrollPane.setBorder(new TitledBorder("Processed Nodes"));

    	textArea = new JTextArea();
	JScrollPane modelScrollPane = new JScrollPane(textArea);
    	modelScrollPane.setPreferredSize(new Dimension(300, 350));
    	modelScrollPane.setBorder(new TitledBorder("SMT Solver output for selected node"));
    	//tableScrollPane.setMinimumSize(minimumSize);
    	textArea.setToolTipText("<html>Note that the input to the SMT solvers is the negated" +
    			"sequent of the selected node. Thus, e.g., the output sat implies that" +
    			"that the respective sequent is falsifiable. Be aware of the possible " +
    			"weakening of sequents that are no directly translatable to FOL.</html>");
	

	
	JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
		tableScrollPane, modelScrollPane);
		splitPane.setOneTouchExpandable(true);
		splitPane.setDividerLocation(300);
	
	getContentPane().add(splitPane);
	pack();
    }
    
    /**@param idx is the row index of {@code tableModel} from which to read the information
     * that shall be displayed in {@code testArea}. If a number smaller than 0 is passed, then the textArea is cleared. */
    protected synchronized void updateTextArea(int idx){
	if(idx<0){
	    textArea.setText("");
	    return;
	}
	StringBuffer sb=new StringBuffer();
	for(int i=1;i<tableModel.getColumnCount();i++){
	    SMTSolverResultWrap val = (SMTSolverResultWrap)tableModel.getValueAt(idx, i);
	    if(val!=null){
		sb.append("------------"+val.r.solverName+"----------\n"+val.r+"\n");
	    }
	}
	textArea.setText(sb.toString());
    }

    
    /** Utility method used by {@code updateTableForNode} */
    private int solverNameToColumn(String solver){
	for(int i=1;i< columnNames.length;i++){
	    if(columnNames[i].equals(solver))
		return i;
	}
	System.err.println("Error DecisionProcedureResultsDialog: Unknown SMT solver: "+solver);
	return -1;//error
    }

    /** Searches the {@code table} or {@code tableModel} for an entry of node {@code n}.
     * If there is no entry/row of the node yet, then a new table row is created.
     * {@code Node.getSMTData} is accessed to fill in the cells of the row
     * with infos from the SMTSolverResults.
     * @return the row index of the node in the table. -1 is returned if something went wrong
     * @author gladisch*/
    protected synchronized int updateTableForNode(Node n){
	    if(n==null || n.proof()!=proof){
		//The displayed proof might have changed by concurrent threads
		return -1;
	    }
	    int rowIdx=-1;
	    //Try to find the row index for this node (if it exists) 
	    for(int i = 0; i<tableModel.getRowCount();i++){
		NodeWrap tmp = (NodeWrap)tableModel.getValueAt(i, 0);
		if(tmp!=null && tmp.n == n){
		    rowIdx=i;
		    break;
		}
	    }
	    
	    if(rowIdx==-1){
		//If no row index was found for the node, then create a new row and get its index
		Object[] row = new Object[columnNames.length];
		row[0] = new NodeWrap(n);
		tableModel.addRow(row);
		rowIdx = tableModel.getRowCount()-1;
	    }
	    	    
	    //Update the row
	    Vector<Object> vect = n.getSMTData();
	    if(vect!=null){
		for(Object o:vect){
		    if(o instanceof SMTSolverResult){
			SMTSolverResult res = (SMTSolverResult)o;
			int i = solverNameToColumn(res.solverName);
			if(i>0){
			    tableModel.setValueAt(new SMTSolverResultWrap(res), rowIdx, i);
			}
		    }
		}
	    }
	    
	    return rowIdx;
    }
    
    /**Call this method when the field {@code proof} changes.
     * @author gladisch*/
    public synchronized int rebuildTableForProof(){
//	int rows = tableModel.getRowCount();
//	for(int i=0;i<rows;i++){
//	    tableModel.removeRow(i);
//	}
//	Strange, the commented out code didn't work for some reason.	
	tableModel.setRowCount(0);
	if(proof!=null){
        	Set<Node> nodes = proof.getNodesWithSMTData();
        	if(nodes!=null){
        	    for(Node n:nodes){
        		updateTableForNode(n);
        	    }
        	}
	}
	return tableModel.getRowCount()-1;
    }
 
    class SMTSolverProofListener extends ProofTreeAdapter implements	KeYSelectionListener {

	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {}

	/**
	 * the selected proof has changed (e.g. a new proof has been loaded)
	 * Warning: The event is called more often (even if the proof does not change).
	 */
	public void selectedProofChanged(KeYSelectionEvent e) {
	    if(proof!=e.getSource().getSelectedProof()){
        	    if(proof!=null){ //The old proof object
        		proof.removeProofTreeListener(this);
        	    }
        	    proof = e.getSource().getSelectedProof();
        	    if(proof!=null && !proof.containsProofTreeListener(this)){
        		System.out.println("added proof tree listener");
        		proof.addProofTreeListener(this);
        	    }
        	    //(new RuntimeException("INFORMATION")).printStackTrace();
        	    int rows = rebuildTableForProof();
        	    if(rows>=0){
        		final int rowIdx=0;
        		table.getSelectionModel().setSelectionInterval(rowIdx,rowIdx);
        		updateTextArea(rowIdx);
        	    }
	    }
	}
	
	public void proofPruned(ProofTreeEvent e) {
	    if(proof!=null){
		    int rowIdx=table.getSelectionModel().getMinSelectionIndex();
            	    int rows = rebuildTableForProof();
        	    if(rows>=0){
        		rowIdx = (0<=rowIdx && rowIdx<=rows)?rowIdx:0;
        		table.getSelectionModel().setSelectionInterval(rowIdx,rowIdx);
        		updateTextArea(rowIdx);
        	    }		
	    }
	}


	    /**If, e.g., an SMT Solver was applied to node/goal referenced in e, then 
	     * this event occurs in order to monitor, e.g. by a dialog, the result
	     * of the SMT solver. The data from the SMT solver can be accessed via.
	     * {@code Node.getCounterExData()}*/
	public synchronized void smtDataUpdate(ProofTreeEvent e){
	    //System.out.println("counterExampleUpdate for node "+ e.getNode().serialNr());
	    if(Main.batchMode || !Main.isVisibleMode()||
		    !DecisionProcedureSettings.getInstance().getShowSMTResDialog()){
		return;
	    }
	    setVisible(true);
	    Node n = e.getNode();
	    final int rowIdx = updateTableForNode(n);
	    updateTextArea(rowIdx);
	    if(rowIdx>=0){
		table.getSelectionModel().setSelectionInterval(rowIdx,rowIdx);
	    }
	};

    }
    
    /**This is to provide a suitable toString method */
    protected class NodeWrap{
	public final Node n;
	NodeWrap(Node n){
	    this.n = n;
	}
	
	public String toString(){
	    return ""+n.serialNr();
	}
    }
    
    /**This is to provide a suitable toString method */
    protected class SMTSolverResultWrap{
	public final SMTSolverResult r;
	SMTSolverResultWrap(SMTSolverResult r){
	    this.r = r;
	}
	
	public String toString(){
	    return ""+ r.isValid();
	}
    }

}
