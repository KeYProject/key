package de.uka.ilkd.key.unittest;

import java.lang.ref.WeakReference;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYSelectionModel;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.TestGenerationDialog;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.unittest.AssGenFac.AssignmentGenerator;
import de.uka.ilkd.key.util.ProgressMonitor;

/**
 * Extend the TestGenerator with methods that send and receive messages with the MethodSelectionDialog.
 * No functionality must be implemented here that is required for test generation. 
 * Functionality related to test generation must be implemented in TestGenerator or subclasses
 * of this class.
 * @author gladisch
 */
public abstract class TestGeneratorGUIInterface extends TestGenerator {

    protected TestGenerationDialog dialog;
    
    protected TestGeneratorGUIInterface(Services serv, String fileName,
            String directory, boolean testing, AssignmentGenerator ag) {
	super(serv, fileName, directory, testing, ag);
    }
    
    public void setMethodSelectionDialog(TestGenerationDialog dialog){
	this.dialog = dialog; 
    }
    
    /** Warning. Background threads and ModelGenerator.modelGenerationTimeout are used internally*/
    synchronized public String  generateTestSuite(final Statement[] code, Term oracle,
	    final List<ModelGenerator> mgs,
	    ImmutableSet<ProgramVariable> programVars, final String methodName,
	    final PackageReference pr,
	    final int timeout) {
	if(Main.isVisibleMode()||Main.testStandalone){
	    Main.getInstance().getProverTaskListener().taskStarted("Generating tests", mgs.size());
	}
	String file = super.generateTestSuite(code, oracle, mgs, programVars, methodName, pr);
	//Main.getInstance().getProverTaskListener().taskFinished(new TaskFinishedInfo());
	return file;
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

