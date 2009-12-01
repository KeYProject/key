package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.util.HashSet;
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
    
    public final static Object[] columnNames = {"Node", CVC3Solver.name, YicesSolver.name, Z3Solver.name, SimplifySolver.name};
    
    public DecisionProcedureResultsDialog(KeYMediator mediator){
	//super(mediator.mainFrame(), "SMT Solver Progress and Results");
	super("SMT Solver Progress and Results");
	this.mediator = mediator;
	listener = new SMTSolverProofListener();
	mediator.addRuleAppListener(listener);
	mediator.addKeYSelectionListener(listener);
	layoutDialog();
	this.setVisible(true);
    }
    
    private void layoutDialog(){
	
	//Todo the columns could be extended dynamically instead of this static initialization
	
	tableModel = new DefaultTableModel(columnNames,0);
	table = new JTable(tableModel);
	table.getSelectionModel().addListSelectionListener(new ListSelectionListener(){

	    public void valueChanged(ListSelectionEvent arg0) {
		int idx = table.getSelectedRow();
		NodeWrap nw = (NodeWrap)tableModel.getValueAt(idx, 0);
		Node n = nw.n;
		mediator.getSelectionModel().setSelectedNode(n);
		StringBuffer sb=new StringBuffer();
		for(int i=1;i<tableModel.getColumnCount();i++){
		    System.out.println("Access "+idx+" "+i);
		    SMTSolverResultWrap val = (SMTSolverResultWrap)tableModel.getValueAt(idx, i);
		    if(val!=null){
			sb.append(val.r);
		    }
		}
		textArea.setText(sb.toString());
            }
	    
	});
	
	
	JScrollPane tableScrollPane = new JScrollPane(table);
	tableScrollPane.setPreferredSize(new Dimension(250, 350));
	//tableScrollPane.setMinimumSize(minimumSize);
	tableScrollPane.setBorder(new TitledBorder("Progressed Nodes"));

    	textArea = new JTextArea();
	JScrollPane modelScrollPane = new JScrollPane(textArea);
    	modelScrollPane.setPreferredSize(new Dimension(250, 350));
    	modelScrollPane.setBorder(new TitledBorder("SMT Solver output for selected node"));
    	//tableScrollPane.setMinimumSize(minimumSize);
	

	
	JSplitPane splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
		tableScrollPane, modelScrollPane);
		splitPane.setOneTouchExpandable(true);
		splitPane.setDividerLocation(250);
	
	getContentPane().add(splitPane);
	pack();
    }
    
    private int solverNameToColumn(String solver){
	for(int i=1;i< columnNames.length;i++){
	    if(columnNames[i].equals(solver))
		return i;
	}
	System.err.println("Error DecisionProcedureResultsDialog: Unknown SMT solver: "+solver);
	return -1;//error
    }

    
 
    class SMTSolverProofListener extends ProofTreeAdapter implements AutoModeListener,
	    RuleAppListener, KeYSelectionListener {

	/** node of the last known current goal */
	private Node lastGoalNode;

	// hack to select Nodes without changing the selection of delegateView
	public boolean ignoreNodeSelectionChange = false;

	/** focused node has changed */
	public void selectedNodeChanged(KeYSelectionEvent e) {
	    System.out.println("selectedNodeChanged");
	    
	    if (!ignoreNodeSelectionChange)
		mediator.getSelectedNode();
	}

	/**
	 * the selected proof has changed (e.g. a new proof has been loaded)
	 */
	public void selectedProofChanged(KeYSelectionEvent e) {
	    Debug.out("ProofTreeView: initialize with new proof");
	    lastGoalNode = null;
	    proof = e.getSource().getSelectedProof();
	    if(!proof.containsProofTreeListener(this)){
		System.out.println("added proof tree listener");
		proof.addProofTreeListener(this);
	    }
	}

	/** invoked if automatic application of rules has started */
	public void autoModeStarted(ProofEvent e) {
	}

	/** invoked if automatic application of rules has stopped */
	public void autoModeStopped(ProofEvent e) {
	    if (mediator.getSelectedProof() == null)
		return; // no proof (yet)
	}

	/** invoked when a rule has been applied */
	public void ruleApplied(ProofEvent e) {
	    System.out.println("ruleApplied");
	    
	    if (proof == e.getSource()) {
		Node origNode = e.getRuleAppInfo().getOriginalNode();
		if(origNode.getCounterExampleData()!=null){
		    System.out.println("SMT Solver generated counter ex for " +origNode.serialNr());
		}else if(origNode.getAppliedRuleApp().rule() instanceof SMTRule ||
			origNode.getAppliedRuleApp().rule() instanceof SMTRuleMulti){
		    System.out.println("SMT Solver closed branch at node "+origNode.serialNr());
		}
	    }else{
		System.err.println("Error:The proof has changed without notice by DecisionProcedureResultsDialog");
	    }
	}
	
	    /**If, e.g., an SMT Solver was applied to node/goal referenced in e, then 
	     * this event occurs in order to monitor, e.g. by a dialog, the result
	     * of the SMT solver. The data from the SMT solver can be accessed via.
	     * {@code Node.getCounterExData()}*/
	public synchronized void counterExampleUpdate(ProofTreeEvent e){
	    System.out.println("counterExampleUpdate for node "+ e.getNode().serialNr());
	    setVisible(true);
	    Node n = e.getNode();
	    int rowIdx=-1;
	    
	    for(int i = 0; i<tableModel.getRowCount();i++){
		NodeWrap tmp = (NodeWrap)tableModel.getValueAt(i, 0);
		if(tmp!=null && tmp.n == n){
		    rowIdx=i;
		    break;
		}
	    }
	    if(rowIdx==-1){
		Object[] row = new Object[columnNames.length];
		row[0] = new NodeWrap(n);
		tableModel.addRow(row);
		rowIdx = tableModel.getRowCount()-1;
	    }
	    
	    
	    Vector<Object> vect = n.getCounterExampleData();
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
	    
	    table.getSelectionModel().setSelectionInterval(rowIdx,rowIdx);
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
