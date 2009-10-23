package de.uka.ilkd.key.unittest;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;

import javax.swing.JList;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MethodSelectionDialog;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.unittest.AssGenFac.AssignmentGenerator;
import de.uka.ilkd.key.unittest.testing.DataStorage;
import de.uka.ilkd.key.visualization.ExecutionTraceModel;
import de.uka.ilkd.key.visualization.ProofVisualization;
import de.uka.ilkd.key.visualization.TraceElement;
import de.uka.ilkd.key.visualization.VisualizationStrategyForTesting;

/** Extends the UnitTestBuilder with methods that send and receive message from the GUI.
 * This is to give the user a better feedback and control over the test generation progress.
 * Do NOT implement functionality required for test generation here. Functionality required
 * for test generation must be implemented in UnitTestBuilder. This is only GUI specific. 
 * @author gladisch
 */
public class UnitTestBuilderGUIInterface extends UnitTestBuilder {
    
    HashSet<Thread> busyThreads= new HashSet<Thread>();
    protected MethodSelectionDialog dialog;
    protected KeYMediator mediator;

    public UnitTestBuilderGUIInterface(KeYMediator mediator){
	this(mediator.getServices(), mediator.getProof(),false);
	this.mediator = mediator;
    }
    
    protected UnitTestBuilderGUIInterface(Services s, Proof p, final boolean testing){
	super(s,p,testing);
    }
    
    public void setMethodSelectionDialog( final MethodSelectionDialog methodSelDialog){
	dialog = methodSelDialog;
    }
    
    /**
     * Initializes the method list for the method selection dialog. These are the methods the user
     * can select to be tested.
     */
    public void initMethodListInBackground(final Proof p){
	MethodListComputation mc= new MethodListComputation(p,dialog.methodList);
	Thread t = new Thread(mc,"Collecting methods from the proof tree");
	mc.setThread(t);
	t.start();
    }
    
   /** This method overwrites the method from UnitTestBuilder in order to report
    * the progress of the evaluation of the method getProgramMethods to the user.
    * @param result intermediate result so far
    * @param finished true when the final result is computed by getProgramMethods.
    */
   protected void getProgramMethods_ProgressNotification(ImmutableSet<ProgramMethod> result, boolean finished){
       String[] list = new String[result.size()+1];
       int i=0;
       list[i++]="Please wait while traces are being computed...";
       for(ProgramMethod pm:result){
	   list[i++]=pm.getName();
       }
       dialog.methodList.setListData(list);
       Thread.currentThread().yield();
   }
   
   /** Executes test generation in a different thread than the calling thread. */
   public void createTestInBackground( final Object[] pms) {
       TestCreationRunnable tcr = new TestCreationRunnable(pms);
       Thread t = new Thread(tcr,"Generating tests for "+pms.toString());
       tcr.setThread(t);
       t.start();
   }
   
   /** called by createTestForNodes.*/
   protected void createTestForNodes_progressNotification1(ExecutionTraceModel etm, Node n){
       System.out.println("Processing Node:"+n.serialNr());
       mediator.getSelectionModel().setSelectedNode(n);
       return;
   }
   
   /** called by createTestForNodes. */
   protected void createTestForNodes_progressNotification2(UnitTestException e){
       System.out.println("Problem Occured:"+e.toString());
       System.out.println("Continuing despite the exception.");
   }

 
   
   /**
    * Use this only in emergency cases.
    */
   public void stopThreads(){
       for(Thread t:busyThreads){
	   t.stop();
	   System.out.println("Thread killed:"+t.getName());
       }
       busyThreads.clear();
       if(tg!=null){
	   tg.clean();
       }
   }
   
   class TrackableRunnable implements Runnable{
       Thread t;
       
       public void setThread(Thread t){
	   busyThreads.add(t);
	   this.t=t;
       }
       
       /**This method is supposed to be called at the end of the overwriting method of is subclasses.
        * The goal is to track in the list busyThreads with threads are still running so they can be terminated 
        * by the user. */
       public void run(){
	   busyThreads.remove(t);
       }
       
   }
   
   class MethodListComputation extends TrackableRunnable{
       final Proof p;
       final JList methodList;
       
       
       public MethodListComputation(final Proof p, final JList methodList){
	   this.p=p;
	   this.methodList = methodList;
       }
       
       public void run() {
  	 final ImmutableSet<ProgramMethod> pms = getProgramMethods(p);
  	 methodList.setListData(pms.toArray(new ProgramMethod[pms.size()]));
  	 super.run();
      }
   }
   
   class TestCreationRunnable extends TrackableRunnable{

       final Object[] pms;

       
       TestCreationRunnable( final Object[] pms){
	this.pms=pms;
       }
       
       public void run(){
	   try {
		    String test;
		    if (pms == null) {
			test = createTestForProof(mediator.getProof());
			dialog.getLatestTests().append(test + " ");
			mediator.testCaseConfirmation(test);
		    } else {
			ImmutableSet<ProgramMethod> pmSet = DefaultImmutableSet
			        .<ProgramMethod> nil();
			for (final Object pm : pms) {
			    pmSet = pmSet.add((ProgramMethod) pm);
			}
			test = createTestForProof(mediator.getProof(),
			        pmSet);
			dialog.getLatestTests().append(test + " ");
			mediator.testCaseConfirmation(test);
		    }
		} catch (final Exception e) {
		    new ExceptionDialog(Main.getInstance(), e);
		}
  
	  super.run();
       }
   }

}
