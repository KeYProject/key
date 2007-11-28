// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//




/*

Uses code by Hans Muller and Kathy Walrath from
http://java.sun.com/products/jfc/tsc/articles/threads/threads2.html

*/


package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.proofevent.IteratorOfNodeReplacement;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.proof.reuse.ReusePoint;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;

/**
 * Applies rules in an automated fashion in a separate thread.
 */
public class ApplyStrategy {

    private static final String PROCESSING_STRATEGY = "Processing Strategy";
    
    private KeYMediator medi;
    /** the proof that is worked with */ 
    private Proof proof;
    /** the maximum of allowed rule applications */
    private int maxApplications;
    
    /** chooses goals to which rules are applied*/
    private IGoalChooser goalChooser;
    
    private SwingWorker worker;
    
    /** number of rules automatically applied */
    private int countApplied = 0;
    private long time;
    
    /** interrupted by the user? */
    private boolean autoModeActive = false;

    private ProofListener proofListener = new ProofListener();
    
    private boolean startedAsInteractive;
    
    private List proverTaskObservers = new ArrayList ();

    private ReusePoint reusePoint;

    /** time in ms after which rule application shall be aborted, -1 disables timeout */
    private long timeout = -1;

    
    // Please create this object beforehand and re-use it.
    // Otherwise the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(KeYMediator medi) {
	this.medi = medi;
        medi.addRuleAppListener( proofListener );
        this.goalChooser = medi.getProfile().getSelectedGoalChooserBuilder().create();
    }
    
    

    /** applies rules that are chosen by the active strategy 
     * @return true iff a rule has been applied, false otherwise
     */
    private synchronized boolean applyAutomaticRule () {
        // Look for the strategy ...
        RuleApp               app = null;
        Goal                  g;
        ReuseListener rl = mediator().getReuseListener();

        if (reusePoint != null) {
            g = reusePoint.target();
            app = reusePoint.getReuseApp();
            g.node().setReuseSource(reusePoint);
            rl.removeRPConsumedMarker(reusePoint.source());
            rl.removeRPConsumedGoal(g);
            ListOfGoal goalList = g.apply(app);
            rl.addRPOldMarkersNewGoals(goalList);
            rl.addRPNewMarkersAllGoals(reusePoint.source());
        } else {
            while ( ( g = goalChooser.getNextGoal () ) != null ) {

                app = g.getRuleAppManager().next();

                if ( app == null )
                    goalChooser.removeGoal ( g );
                else
                    break;
            }
            if (app == null) return false;            
            rl.removeRPConsumedGoal(g);                
            rl.addRPOldMarkersNewGoals(g.apply(app));
        }

        if (rl.reusePossible()) reusePoint = rl.getBestReusePoint();
        else reusePoint = null;

        return true;
    }


    /**
     * applies rules until this is no longer
     * possible or the thread is interrupted.
     */
    Object doWork() {
        time = System.currentTimeMillis();
        try{
	   Debug.out("Strategy started.");
	   while (!maxRuleApplicationOrTimeoutExceeded()) {     
               if (!applyAutomaticRule()) {
                   // no more rules applicable
                   break;
               }
               countApplied++;
               fireTaskProgress ();
               if (Thread.interrupted()) throw new InterruptedException();
	   }
        } catch (InterruptedException e) {
            return "Interrupted";  // SwingWorker.get() returns this
        } catch (Throwable t) { // treated later in finished()
            System.err.println(t);
            t.printStackTrace();
            return "Error";
	} finally{
	    time = System.currentTimeMillis()-time;
	    Debug.out("Strategy stopped.");
	    Debug.out("Applied ", countApplied);
	    Debug.out("Time elapsed: ", time);
        }
        return "Done.";
    }


    /**
     * returns if the maximum number of rule applications or
     * the timeout has been reached
     * @return true if automatic rule application shall be stopped because the maximal
     * number of rules have been applied or the time out has been reached
     */
    private boolean maxRuleApplicationOrTimeoutExceeded() {
        return countApplied >= maxApplications || 
           timeout>=0 ? 
                System.currentTimeMillis() - time >= timeout : false;
    }


    private synchronized void fireTaskStarted () {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            ((ProverTaskListener)proverTaskObservers.get(i))
                .taskStarted(PROCESSING_STRATEGY, maxApplications);
        }
    }

    private synchronized void fireTaskProgress () {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            ((ProverTaskListener)proverTaskObservers.get(i))
                .taskProgress(countApplied);
        }
    }

    private synchronized void fireTaskFinished () {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            ((ProverTaskListener)proverTaskObservers.get(i)).taskFinished();
        }
    }


    private void init(ListOfGoal goals, int maxSteps, long timeout) {
        proof = medi.getProof();
        maxApplications = maxSteps;
        this.timeout = timeout;
        countApplied = 0;
        goalChooser.init ( proof, goals );
        setAutoModeActive(true);
        startedAsInteractive = !mediator().autoMode();
        if ( startedAsInteractive ) {
            mediator().stopInterface(true);
        }
        mediator().setInteractive(false);
        fireTaskStarted ();
    }
    

    private KeYMediator mediator() {
        return medi;
    }
    


    public void start(ListOfGoal goals, int maxSteps, long timeout) {
        init(goals, maxSteps, timeout);

        worker = new AutoModeWorker();
        worker.start();
    }

    /**
     * Called by the "Stop" button, interrupts the worker thread 
     * which is running this.doWork().  Note that the doWork() 
     * method handles InterruptedExceptions cleanly.
     */
    public void stop () {
        worker.interrupt();
    }
    
    
    private void displayResults ( Main main, String timeString ) {
        String message;
        int closed = mediator().getNrGoalsClosedByAutoMode();
        
        // display message in the status bar
        
        if ( countApplied != 0 ) {
            message = "Strategy: Applied " + countApplied + " rule";
            if ( countApplied != 1 ) message += "s";
            message += " (" + timeString + " sec), ";
            message += " closed " + closed + " goal";
            if ( closed != 1 ) message += "s";             
            message += ", "+main.displayedOpenGoalNumber ();
            message += " remaining"; 
            main.setStatusLine ( message );
        }
                       
        mediator().resetNrGoalsClosedByHeuristics();
    }

    private void finishedBatchMode (Object result) {
        if ( Main.statisticsFile != null )
            printStatistics ( Main.statisticsFile, result );
        
        if ("Error".equals ( result ) ) {
            // Error in batchMode. Terminate with status -1.
            System.exit ( -1 );
        }
        
        // Save the proof before exit.
        
        String baseName = Main.fileNameOnStartUp;
        int idx = baseName.indexOf(".key");        
        if (idx == -1) {
            idx = baseName.indexOf(".proof");
        }        
        baseName = baseName.substring(0, idx==-1 ? baseName.length() : idx);
                
        File f; 
        int counter = 0;
        do {           
            
            f = new File(baseName + ".auto."+ counter +".proof");
            counter++;
        } while (f.exists());
                        
        Main.getInstance ().saveProof ( f.getAbsolutePath() );
        if (proof.openGoals ().size () == 0) {
            // Says that all Proofs have succeeded
            if (proof.getBasicTask().getStatus().getProofClosedButLemmasLeft()) {
                // Says that the proof is closed by depends on (unproved) lemmas                
                System.exit ( 2 ); 
            }
            System.exit ( 0 ); 
        } else {
            // Says that there is at least one open Proof
            System.exit ( 1 );
        }
    }



    private void printStatistics(String file, Object result) {
        try {
            final FileWriter statistics = new FileWriter ( file, true );
            final PrintWriter statPrinter = new PrintWriter ( statistics );
            
            String fileName = Main.fileNameOnStartUp;
            final int slashIndex = fileName.lastIndexOf ( "examples/" );
            if ( slashIndex >= 0 )
                fileName = fileName.substring ( slashIndex );
            
            statPrinter.print ( fileName + ", " );
            if ("Error".equals ( result ) )
                statPrinter.println ( "-1, -1" );
            else
                statPrinter.println ( "" + countApplied + ", " + time );                
            statPrinter.close();
        } catch ( IOException e ) {}
    }
    
    public synchronized void addProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers.add(observer);
    }

    public synchronized void removeProverTaskObserver(ProverTaskListener observer) {
        proverTaskObservers.remove(observer);
    }


    
    /* Invoking start() on the SwingWorker causes a new Thread
     * to be created that will call construct(), and then
     * finished().  Note that finished() is called even if
     * the worker is interrupted because we catch the
     * InterruptedException in doWork().
     */
    private class AutoModeWorker extends SwingWorker {
    
        public Object construct() {
            Object res = doWork();
	    return res;
        }

        public void finished() {
            setAutoModeActive(false);
	    fireTaskFinished ();
	    String timeString = "" + (time/1000)+"."+((time%1000)/100);

	    final Object result = get ();
        
	    if (Main.batchMode) {
                // This method does not return.
                finishedBatchMode (result);
                Debug.fail ( "Control flow should not reach this point." );
	    }
        
            if ("Error".equals ( result )) {
                mediator ().startInterface ( true );
                mediator ().notify
                (new GeneralFailureEvent("An exception occurred during" 
                        + " strategy execution."));               
            } else {
                if (startedAsInteractive) mediator().startInterface(true);
            }
            
            mediator().setInteractive( true );
            displayResults ( Main.getInstance (), timeString );
        }
    }
    
    private class ProofListener implements RuleAppListener {
    
	/** invoked when a rule has been applied */
	public void ruleApplied(ProofEvent e) {
            if (!isAutoModeActive()) return;
	    RuleAppInfo rai = e.getRuleAppInfo ();
	    if ( rai == null )
		return;

	    synchronized ( ApplyStrategy.this ) {
		ListOfGoal                newGoals = SLListOfGoal.EMPTY_LIST;
		IteratorOfNodeReplacement it       = rai.getReplacementNodes ();
		Node                      node;
		Goal                      goal;          
                
		while ( it.hasNext () ) {
		    node = it.next ().getNode ();
		    goal = proof.getGoal ( node );
		    if ( goal != null )
			newGoals = newGoals.prepend ( goal );
		}

                goalChooser.updateGoalList ( rai.getOriginalNode (), newGoals );
	    }
	}
	
    }

    public boolean isAutoModeActive() {
        return autoModeActive;
    }



    public void setAutoModeActive(boolean autoModeActive) {
        this.autoModeActive = autoModeActive;
    }    

}
