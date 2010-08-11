// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.HashSet;

import javax.swing.JList;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.TestGenerationDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.visualization.ExecutionTraceModel;

/** Extends the UnitTestBuilder with methods that send and receive message from the GUI.
 * This is to give the user a better feedback and control over the test generation progress.
 * Do NOT implement functionality required for test generation here. Functionality required
 * for test generation must be implemented in UnitTestBuilder. This is only GUI specific. 
 * @author gladisch
 */
public class UnitTestBuilderGUIInterface extends UnitTestBuilder {
    
    HashSet<Thread> busyThreads= new HashSet<Thread>();
    /**Warning this field is allowed to be null! It is null when running KeY with the option "testing" */
    protected TestGenerationDialog dialog;
    protected KeYMediator mediator;

    public UnitTestBuilderGUIInterface(KeYMediator mediator){
	this(mediator.getServices(), mediator.getProof(),false);
	this.mediator = mediator;
	this.dialog = null;
    }

    public UnitTestBuilderGUIInterface(KeYMediator mediator, TestGenerationDialog msDialog){
	this(mediator.getServices(), mediator.getProof(),false);
	this.mediator = mediator;
	this.dialog = msDialog;
    }
    
    protected UnitTestBuilderGUIInterface(Services s, Proof p, final boolean testing){
	super(s,p,testing);
    }
    
   
    
    /**
     * Initializes the method list for the method selection dialog. These are the methods the user
     * can select to be tested.
     */
    public void initMethodListInBackground(final Proof p){
	MethodListComputation mc= new MethodListComputation(p,(dialog==null)?new JList():dialog.methodList);
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
       if(dialog!=null){
           String[] list = new String[result.size()+1];
           int i=0;
           list[i++]="Please wait while traces are being computed...";
           for(ProgramMethod pm:result){
    	   list[i++]=pm.getName();
           }
           dialog.methodList.setListData(list);
           Thread.yield();
       }else if(Main.isVisibleMode() || Main.testStandalone){
	   String txt = finished? "Computation of traces has finished" :"Traces are being computed...";
	   Main.getInstance().setStatusLine(txt);
       }
   }
   
   /** Executes test generation in a different thread than the calling thread. */
   public void createTestInBackground( final Object[] pms) {
       TestCreationRunnable tcr = new TestCreationRunnable(pms);
       Thread t = new Thread(tcr,"Generating tests for "+ ((pms==null)?"proof":pms.toString()));
       tcr.setThread(t);
       t.start();
   }
   
   /** called by createTestForNodes.*/
   protected void createTestForNodes_progressNotification0(int nodeCounter, Node n){
       String txt = "("+nodeCounter+") Compute an execution trace for node:"+n.serialNr();
       if(dialog!=null && Main.isVisibleMode()){
	   dialog.msg(txt, n, null);
       }
       if(Main.testStandalone){
	   Main.getInstance().setStatusLine(txt);
       }
       
       return;
   }

   /** called by createTestForNodes.*/
   protected void createTestForNodes_progressNotification1(ExecutionTraceModel etm, Node pathConditionNode, Node originalNode){
       if(dialog!=null && Main.isVisibleMode())
	   dialog.goodMsg("Selected execution trace for "+originalNode.serialNr()+
		   ". Using path condition from "+pathConditionNode.serialNr(), 
		   pathConditionNode, 
		   null);
       //System.out.println("Selected execution trace for node:"+n.serialNr()+ "  Last node of execution trace is: "+etm.getLastNode().serialNr());
//       if(dialog!=null && dialog.trackProgressInViewport.isSelected()){
//	   mediator.getSelectionModel().setSelectedNode(n);
//       }
       return;
   }
   
   /** called by createTestForNodes. */
   protected void createTestForNodes_progressNotification2(UnitTestException e){
       String msg="Problem Occured:"+e.toString()+ "\n Continuing despite the exception";
       if(dialog!=null && Main.isVisibleMode()){
	   dialog.error(msg, null, null);
       }
   }

 
   
   /**
    * Use this only in emergency cases.
    */
   public void stopThreads(){
       for(Thread t:busyThreads){
	   t.stop();
	   String msg = "Thread killed:"+t.getName();
	   if(dialog!=null && Main.isVisibleMode())
	       dialog.msg(msg);
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
  	 if(dialog!=null){
          	 dialog.pack();
          	 dialog.repaint();
  	 }
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
			//dialog.getLatestTests().append(test + " ");
			mediator.testCaseConfirmation(test);
		    } else {
			ImmutableSet<ProgramMethod> pmSet = DefaultImmutableSet
			        .<ProgramMethod> nil();
			for (final Object pm : pms) {
			    pmSet = pmSet.add((ProgramMethod) pm);
			}
			test = createTestForProof(mediator.getProof(),
			        pmSet);
			//dialog.getLatestTests().append(test + " ");
			mediator.testCaseConfirmation(test);
		    }
		} catch (final Exception e) {
		    if(Main.isVisibleMode()){
			new ExceptionDialog(Main.getInstance(), e);
		    }else{
			throw new RuntimeException(e);
		    }
		}
  
	  super.run();
       }
   }
   
   protected ModelGenerator getModelGenerator(final String executionTraceModel, final Node node,
	    final Node originalNode) {
	return new ModelGeneratorGUIInterface(serv, uc, node, executionTraceModel, originalNode);
   }


}
