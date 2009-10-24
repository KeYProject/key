package de.uka.ilkd.key.unittest;

import java.lang.ref.WeakReference;

import de.uka.ilkd.key.gui.KeYSelectionModel;
import de.uka.ilkd.key.gui.MethodSelectionDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.unittest.AssGenFac.AssignmentGenerator;

/**
 * Extend the TestGenerator with methods that send and receive messages with the MethodSelectionDialog.
 * No functionality must be implemented here that is required for test generation. 
 * Functionality related to test generation must be implemented in TestGenerator or subclasses
 * of this class.
 * @author gladisch
 */
public abstract class TestGeneratorGUIInterface extends TestGenerator {

    protected MethodSelectionDialog dialog;
    
    protected TestGeneratorGUIInterface(Services serv, String fileName,
            String directory, boolean testing, AssignmentGenerator ag) {
	super(serv, fileName, directory, testing, ag);
    }
    
    public void setMethodSelectionDialog(MethodSelectionDialog dialog){
	this.dialog = dialog; 
    }
    
    
    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads. */
    protected void generateTestSuite_progressNotification1(
	    int count, int totalCount,WeakReference<ModelGenerator> refMG){
	try{
	    Node n =refMG.get().originalNode;
		System.out.println("Generating model for node:"+n.serialNr());
	       if(dialog!=null && dialog.trackProgressInViewport != null && 
		       dialog.trackProgressInViewport.isSelected()){
		    dialog.mediator.getSelectionModel().setSelectedNode(n);
	       }
	}catch(NullPointerException e){
	    //NullPointerException is ok, e.g. if we are in non-gui mode or when KeY is tested
	}
	return;
	}

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads.  */
    protected void generateTestSuite_progressNotification2(
	    int count, int totalCount, WeakReference<ModelGenerator> refMG, WeakReference<Model[]> models, 
	    boolean createModelsSuccess, boolean terminated){
	if(terminated)
	    System.out.println("("+count+"/"+totalCount+") modelGeneration thread has timed out for node:"+refMG.get().originalNode.serialNr());
	if(models.get()==null || models.get().length==0)
	    System.out.println("("+count+"/"+totalCount+") no model generated for node:"+refMG.get().originalNode.serialNr());

	return;}

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads.*/
    protected void generateTestSuite_progressNotification3(
	    int count, int totalCount, WeakReference<ModelGenerator> refMG, WeakReference<Model[]> models, MethodDeclaration mDecl){
	    System.out.println("("+count+"/"+totalCount+") test method generated for node "+refMG.get().originalNode.serialNr());
	return;}

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads. */
    protected void generateTestSuite_progressNotification4(
	    int count, int totalCount, Exception e, WeakReference<ModelGenerator> refMG, WeakReference<Model[]> models, MethodDeclaration mDecl){
	System.out.println("("+count+"/"+totalCount+") An error occured while generating test method for node "+refMG.get().originalNode.serialNr()+
		" \n Test generation will however continue. The error was "+e.toString()+ " \n");
	e.printStackTrace();
    }

  

}
