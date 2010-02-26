package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;

import javax.swing.AbstractAction;
import javax.swing.ButtonGroup;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;
import javax.swing.table.DefaultTableModel;

import de.uka.ilkd.key.bugdetection.BugDetector;
import de.uka.ilkd.key.bugdetection.FalsifiabilityPreservation;
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


/**This dialog (or window) displays a table that associates nodes with results from SMT solvers
 * and falsifiability preservation information. If a node is falsifiable and 
 * falsifiability is preserved from that node to the root, then also the root is falsifiable
 * and the program has a bug. 
 * <p>The data that is displayed by this dialog is stored in the currently selected {@code Proof}
 * object. This class has a subclass that is derived from
 * ProofTreeAdapter and KeYSelectionListener. Extend and/or register these listeners if 
 * you want to update this Dialog. 
 * <p>The visibility of this window is controlled via Main.decProcResDialog.
 * @see de.uka.ilkd.key.bugdetection.BugDetector
 * @author gladisch */
public class SMTResultsAndBugDetectionDialog extends JFrame {

    private static final long serialVersionUID = -355104767895519452L;
    private final KeYMediator mediator;
    private JTextArea textArea;
    private DefaultTableModel tableModel;
    private JTable table; 
    /**The current proof object in focus */
    private Proof proof;
    private final SMTSolverProofListener listener;
    private static SMTResultsAndBugDetectionDialog instance;
    
    /**A column name abbreviating "Falsifiability Preservation up to Node ..."*/
    private final static String FP_TO_NODE = "FP to Node";
    
    /**Warning: when modifying this array, be aware to update the code locations where
     * this field is accessed. Some implicit assumptions are made on the content of this array. */
    public final static Object[] columnNames = {"Node", CVC3Solver.name, YicesSolver.name, Z3Solver.name, SimplifySolver.name, FP_TO_NODE};
    
    private BugDetector bd = BugDetector.DEFAULT;

    /**The window is set visible by the ProofTree event smtDataUpdate */
    protected SMTResultsAndBugDetectionDialog(KeYMediator medi){
	//super(mediator.mainFrame(), "SMT Solver Progress and Results");
	super("SMT Solver Results and Bug Detection Dialog");
	this.mediator = medi;
	listener = new SMTSolverProofListener();
	//mediator.addRuleAppListener(listener);
	mediator.addKeYSelectionListener(listener);
	layoutWindow();
	table.getSelectionModel().addListSelectionListener(new ListSelectionListener(){

	    public void valueChanged(ListSelectionEvent arg0) {
		//assert arg0.getSource()==table:"arg0.getSource()!=table"; //A table cell may be the source
		assert table.getModel()==tableModel:"table.getModel()!=tableModel";
		int idx = table.getSelectedRow();
		
		if(idx < tableModel.getRowCount()){
		    if(idx>=0){
        		NodeWrap nw = (NodeWrap)tableModel.getValueAt(idx, 0);
        		Node n = nw.n;
        		//System.out.println("Selecting node:"+n.serialNr());
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
    public static SMTResultsAndBugDetectionDialog getInstance(KeYMediator medi){
	if(instance==null){
	    if(medi==null){
		return null;
	    }
	    instance = new SMTResultsAndBugDetectionDialog(medi);
	}
	return instance;
    }
    
    
    private void layoutWindow(){
	
	this.setJMenuBar(new JMenuBar());
        JMenuBar menuBar = getJMenuBar();
        JMenu fpMenu = new JMenu("Falsifiability Preservation");
        ButtonGroup group = new ButtonGroup();
        String tooltip1 = "<html>In order to check falsifiability preservation of a branch,<br>" +
				"right-click on a node in the proof tree and select \"Bug Detection\".</html>";
        JRadioButtonMenuItem optFPInteractive = new JRadioButtonMenuItem("Prove interactively",bd.fpCheckInteractive);
	    optFPInteractive.setToolTipText(tooltip1);
	    fpMenu.add(optFPInteractive, 0);
	    group.add(optFPInteractive);
	JRadioButtonMenuItem optFPInBackground = new JRadioButtonMenuItem("Prove in background",!bd.fpCheckInteractive);
            optFPInBackground.setToolTipText(tooltip1);
	    fpMenu.add(optFPInBackground, 1);
	    optFPInBackground.setActionCommand("FPbackground");
	    group.add(optFPInBackground);	
	    
	    AbstractAction aAction = new AbstractAction(){
		public void actionPerformed(ActionEvent arg0) {
		    if(arg0.getActionCommand().equalsIgnoreCase("FPbackground")){
			bd.fpCheckInteractive=false;
			System.out.println("Prove FP in background");
		    }else{
			bd.fpCheckInteractive=true;
			System.out.println("Prove FP interactively");
		    }
                }
	    };
	    optFPInteractive.addActionListener(aAction);
	    optFPInBackground.addActionListener(aAction);
        menuBar.add(fpMenu);

	//Todo the columns could be extended dynamically instead of this static initialization
	
	tableModel = new DefaultTableModel(columnNames,0);
	table = new JTable(tableModel);
	table.setToolTipText("<html><p>Solver outputs are TRUE, UNKNOWN, FALSIFIABLE.<br> " +
			"Note that weakening is performed, when the node contains<br>" +
			"formulas or terms not directly translatable to FOL, such as<br>" +
			"dynamic logic formulas. In this case the result FALSIFIABLE is <br>" +
			"not sound and you should apply KeY rules to eliminate such formulas<br></p>" +
			
			"<p>The column \"FP to Node\" denotes the closest node to the root<br>" +
			"(on the branch of \"Node\") up to which falsifiability is preserved.<br>" +
			"Thus if \"Node\" is falsifiable and falsifiability is preserved from<br>" +
			"the node in column \"Node\" up to the root (FP to Node = 1),<br>" +
			"then the root node is falsifiable and the program has a bug.</p></html>");
	
	
	JScrollPane tableScrollPane = new JScrollPane(table);
	tableScrollPane.setPreferredSize(new Dimension(450, 350));
	//tableScrollPane.setMinimumSize(minimumSize);
	tableScrollPane.setBorder(new TitledBorder("Processed Nodes"));

    	textArea = new JTextArea();
	JScrollPane modelScrollPane = new JScrollPane(textArea);
    	modelScrollPane.setPreferredSize(new Dimension(300, 350));
    	modelScrollPane.setBorder(new TitledBorder("SMT Solver output for selected node"));
    	//tableScrollPane.setMinimumSize(minimumSize);
    	textArea.setToolTipText("<html>Note that the input to the SMT solvers is the negated<br>" +
    			"sequent of the selected node. Thus, e.g., the output sat implies that<br>" +
    			"that the respective sequent is falsifiable. Be aware of the possible<br>" +
    			"weakening of sequents that are no directly translatable to FOL.</html>");
	

	
	JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
		tableScrollPane, modelScrollPane);
		splitPane.setOneTouchExpandable(true);
		splitPane.setDividerLocation(450);
	
	getContentPane().add(splitPane);
	pack();
    }
    
    /**@param idx is the row index of {@code tableModel} from which to read the information
     * that shall be displayed in {@code testArea}. If a number smaller than 0 is passed, then the textArea is cleared. */
    protected  void updateTextArea(int idx){
	synchronized(tableModel){
	    	Boolean falsifiable=null; //determines if at lease one SMTSolverResult is falsifiable.
        	if(idx<0){
        	    textArea.setText("");
        	    return;
        	}
        	StringBuffer sb=new StringBuffer();
        	for(int i=1;i<columnNames.length-1;i++){
        	    SMTSolverResultWrap val = (SMTSolverResultWrap)tableModel.getValueAt(idx, i);
        	    if(val!=null){
        		sb.append("------------").append(val.r.solverName).append("----------\n").append(val.r).append("\n");
                    	if(val.r.isValid() == SMTSolverResult.ThreeValuedTruth.FALSIFIABLE){
                    	    falsifiable = true;
                    	}else if(val.r.isValid() == SMTSolverResult.ThreeValuedTruth.TRUE){
                    	    falsifiable = false;
                    	}
        	    }
        	}
        	
        	//NodeWrap uptoNode = (NodeWrap)tableModel.getValueAt(idx, columnNames.length-1);
        	NodeWrap nw = (NodeWrap)tableModel.getValueAt(idx, 0);
        	FalsifiabilityPreservation fp = getFPData(nw.n);
        	if(fp!=null){
        	    sb.insert(0, fp.getMessage(falsifiable)+"\n\n");
//        	    Node uptoNode = fp.get_Upto_Node();
//        	    if(uptoNode!=null && uptoNode.root() 
//        		    && falsifiable){
//        		sb.insert(0, "The target program has a bug on the selected trace!\n " +
//        			"This is guaranteed because the node "+nw.n.serialNr()+" is falsifiable and fasifiability is preserved up to the root node.\n\n");
//        	    }
        	}
        	
        	textArea.setText(sb.toString());
	}
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
    
    private int fpToNodeColumn(){
	if(columnNames[5]!=FP_TO_NODE){
	    throw new RuntimeException();
	}
	return 5;
    }

    private static FalsifiabilityPreservation getFPData(Node n){
	    Vector<Object> vect = n.getSMTandFPData();
	    if (vect == null) {
		return null;
	    }
	    for (Object o : vect) {
		if (o instanceof FalsifiabilityPreservation) {
		    return (FalsifiabilityPreservation)o;
		}
	    }
	    return null;
    }
    
    /**
     * Searches the {@code table} or {@code tableModel} for an entry of node
     * {@code n}. If there is no entry/row of the node yet, then a new table row
     * is created. {@code Node.getSMTData} is accessed to fill in the cells of
     * the row with infos from the SMTSolverResults.
     * 
     * @return the row index of the node in the table. -1 is returned if
     *         something went wrong
     * @author gladisch
     */
    protected int updateTableForNode(Node n) {
	synchronized (tableModel) {
	    if (n == null || n.proof() != proof) {
		// The displayed proof might have changed by concurrent threads
		return -1;
	    }
	    int rowIdx = -1;

	    //First check if there is data for the node that should be displayed in the table
	    //Data that should not be displayed is e.g. FPConditions.
	    Vector<Object> vect = n.getSMTandFPData();
	    if (vect == null) {
		return -1;
	    }
	    boolean dataToDisplay = false;
	    for (Object o : vect) {
		if (	o instanceof SMTSolverResult
		     || o instanceof FalsifiabilityPreservation) {
		    dataToDisplay = true;
		    break;
		}
	    }
	    if(!dataToDisplay){
		return -1;
	    }

	    // Try to find the row index for this node (if it exists)
	    for (int i = 0; i < tableModel.getRowCount(); i++) {
		NodeWrap tmp = (NodeWrap) tableModel.getValueAt(i, 0);
		if (tmp != null && tmp.n == n) {
		    rowIdx = i;
		    break;
		}
	    }

	    if (rowIdx == -1) {
		// If no row index was found for the node, then create a new row
		// and get its index
		Object[] row = new Object[columnNames.length];
		row[0] = new NodeWrap(n);
		tableModel.addRow(row);
		rowIdx = tableModel.getRowCount() - 1;
	    }

	    // Update the row
	    for (Object o : vect) {
		if (o instanceof SMTSolverResult) {
		    SMTSolverResult res = (SMTSolverResult) o;
		    int i = solverNameToColumn(res.solverName);
		    if (i > 0) {
			tableModel.setValueAt(new SMTSolverResultWrap(res),
			        rowIdx, i);
		    }
		} else if (o instanceof FalsifiabilityPreservation) {
		    FalsifiabilityPreservation fp = (FalsifiabilityPreservation) o;
		    tableModel.setValueAt(new NodeWrap(fp.get_Upto_Node()),
			    rowIdx, fpToNodeColumn());
		}
	    }

	    return rowIdx;
	}
    }
    
    /**Call this method when the field {@code proof} changes.
     * @author gladisch*/
    public  int rebuildTableForProof(){
	synchronized(tableModel){
        //	int rows = tableModel.getRowCount();
        //	for(int i=0;i<rows;i++){
        //	    tableModel.removeRow(i);
        //	}
        //	Strange, the commented out code didn't work for some reason.
        	tableModel.setRowCount(0);
        	if(proof!=null){
                	Set<Node> nodes = proof.getNodesWithSMTandFPData();
                	if(nodes!=null){
                	    for(Node n:nodes){
                		updateTableForNode(n);
                	    }
                	}
        	}
        	return tableModel.getRowCount()-1;
	}
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
	    if(rowIdx!=-1){
		//the method can handle -1 but it would delete the test in the text area. 
		//Here we want to keep the text if the table was not updated.
		updateTextArea(rowIdx);
	    }
//	The commented out code causes deadlocks.  It was supposed to do on-the-fly selection of table rows and nodes. 
//	    updateTextArea(rowIdx);
//	    if(rowIdx>=0){
//		table.getSelectionModel().setSelectionInterval(rowIdx,rowIdx);
//	    }
	}

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
