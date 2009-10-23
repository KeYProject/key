package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.gui.MethodSelectionDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
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
    protected void generateTestSuite_processNotification1(
	    int count, int totalCount, ModelGenerator mg){
	dialog.mediator.getSelectionModel().setSelectedNode(mg.originalNode);
	return;}

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads.  */
    protected void generateTestSuite_processNotification2(
	    int count, int totalCount, ModelGenerator mg, Model[] models, 
	    boolean createModelsSuccess, boolean terminated){
	if(terminated)
	    System.out.println("("+count+"/"+totalCount+") modelGeneration thread has timed out for node:"+mg.originalNode.serialNr());
	return;}

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads.*/
    protected void generateTestSuite_processNotification3(
	    int count, int totalCount, ModelGenerator mg, Model[] models, MethodDeclaration mDecl){
	    System.out.println("("+count+"/"+totalCount+") test method generated for node "+mg.originalNode.serialNr());
	return;}

    /**When generateTestSuite() is executed on a separate thread, then this notification method
     * is called in order to report the progress of computation to other threads. */
    protected void generateTestSuite_processNotification4(
	    int count, int totalCount, Exception e, ModelGenerator mg, Model[] models, MethodDeclaration mDecl){
	System.out.println("("+count+"/"+totalCount+") An error occured while generating test method for node "+mg.originalNode.serialNr()+
		" \n Test generation will however continue. The error was "+e.toString());
    }

  

}
