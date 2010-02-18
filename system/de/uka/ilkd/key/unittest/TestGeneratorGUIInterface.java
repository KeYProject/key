package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.TestGenerationDialog;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.proof.Node;

/**
 * Extend the TestGenerator with methods that send and receive messages with the MethodSelectionDialog.
 * No functionality must be implemented here that is required for test generation. 
 * Functionality related to test generation must be implemented in TestGenerator or subclasses
 * of this class.
 * @author gladisch
 */
public  class TestGeneratorGUIInterface  {

    protected TestGenerationDialog dialog;
    
    
    public void setMethodSelectionDialog(TestGenerationDialog dialog){
	this.dialog = dialog; 
    }
    
    /** Warning. Background threads and ModelGenerator.modelGenerationTimeout are used internally*/
    synchronized void generateTestSuite_progressNotification0(final int totalCount) {
	if(Main.isVisibleMode()||Main.testStandalone){
	    Main.getInstance().getProverTaskListener().taskStarted("Generating tests", totalCount);
	}
    }
    
    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads. */
    protected void generateTestSuite_progressNotification1(int count,
	    int totalCount, ModelGenerator refMG) {
	try {
	    Node n = refMG.node;
	    Node originalNode = refMG.originalNode;
    
	    if (dialog != null  && Main.isVisibleMode()){
		dialog.msg("(" + count + "/" + totalCount+ ") Generating model for node " + n.serialNr()
			+ ". Selected child node was:"+originalNode.serialNr(), n, null);
		if(dialog.trackProgressInViewport != null  && dialog.trackProgressInViewport.isSelected()) {
			dialog.mediator.getSelectionModel().setSelectedNode(n);
		}
	    }
	} catch (NullPointerException e) {
	    // NullPointerException is ok, e.g. if we are in non-gui mode or
	    // when KeY is tested
	}

    }

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads.  */
    protected void generateTestSuite_progressNotification2(int count,
	    int totalCount, ModelGenerator refMG,
	    Model[] models, boolean createModelsSuccess,
	    boolean terminated) {
	if (terminated) {
	    Node n = refMG.node;
	    String msg = "(" + count + "/" + totalCount
		    + ") modelGeneration thread has timed out for node:"
		    + n.serialNr();
	    if (dialog != null && Main.isVisibleMode())
		dialog.badMsg(msg, n, null);
	}

	if (models == null || models.length == 0) {
	    Node n = refMG.node;
	    String msg = "(" + count + "/" + totalCount
		    + ") NO model generated for node:"
		    + n.serialNr();
	    if (dialog != null && Main.isVisibleMode())
		dialog.badMsg(msg, n, null);
	}

    }
    
    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads.  */
    protected void generateTestSuite_progressNotification2b(
	    int count, int totalCount, ModelGenerator refMG,EquivalenceClass ec){
	    Node n = refMG.node;
	    String msg = "(" + count + "/" + totalCount
		    + ") "+n.serialNr()+"  No test data for equivalence class "+ ec.toString();
	    if (dialog != null && Main.isVisibleMode())
		dialog.badMsg(msg, n, null);
	    }
	


    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads.*/
    protected void generateTestSuite_progressNotification3(
	    int count, int totalCount, ModelGenerator refMG, Model[] models, MethodDeclaration mDecl){
	    Node n = refMG.node;
	    String msg = "("+count+"/"+totalCount+") test method generated for node "+n.serialNr();
	    if(Main.isVisibleMode()||Main.testStandalone){
		Main.getInstance().getProverTaskListener().taskProgress(count);
		if (dialog != null ){
		    dialog.goodMsg(msg, n, null);
		}
	    }
    }

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads. */
    protected void generateTestSuite_progressNotification4(
	    int count, int totalCount, Exception e, ModelGenerator refMG, Model[] models, MethodDeclaration mDecl){
	Node n = refMG.node;
	if (dialog != null && Main.isVisibleMode()){
	dialog.error("("+count+"/"+totalCount+") An error occured while generating test method for node "+n.serialNr()+
			" \n Test generation will however continue. The error was "+e.toString()+ " \n", n, null);
	}
	e.printStackTrace();

    }

  

}

