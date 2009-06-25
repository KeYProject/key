// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import java.util.ArrayList;
import java.util.List;

import javax.swing.JDialog;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.JavaTestGenerationProfile;
import de.uka.ilkd.key.proof.proofevent.IteratorOfNodeReplacement;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.VBTStrategy;
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
    
    private List<ProverTaskListener> proverTaskObservers = new ArrayList<ProverTaskListener> ();

    /** time in ms after which rule application shall be aborted, -1 disables timeout */
    private long timeout = -1;
    
    private String usedCoalChooserOptionsKey="";

    
    // Please create this object beforehand and re-use it.
    // Otherwise the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(KeYMediator medi) {
	this.medi = medi;
        medi.addRuleAppListener( proofListener );        
    }
    
    

    /** applies rules that are chosen by the active strategy 
     * @return true iff a rule has been applied, false otherwise
     */
    private synchronized boolean applyAutomaticRule () {
        // Look for the strategy ...
        RuleApp               app = null;
        Goal                  g;
        while ( ( g = goalChooser.getNextGoal () ) != null ) {                
            app = g.getRuleAppManager().next();

            if (app == null) {
        	if (medi.getProof().getSettings().getStrategySettings()
                                   .getActiveStrategyProperties().getProperty(
                                    StrategyProperties.STOPMODE_OPTIONS_KEY)
                            .equals(StrategyProperties.STOPMODE_NONCLOSE)) {
                    // iff Stop on non-closeable Goal is selected a little
                    // popup is generated and proof is stopped
                    JOptionPane pane = new JOptionPane(
                            "Couldn't close Goal Nr. "
                                    + g.node().serialNr()
                                    + " automatically",
                            JOptionPane.INFORMATION_MESSAGE,
                            JOptionPane.DEFAULT_OPTION);
                    JDialog dialog = pane.createDialog(medi.mainFrame(),
                            "The KeY Project");
                    dialog.setVisible(true);
                    medi.goalChosen(g);
                    return false;
        	}
        	goalChooser.removeGoal(g);
            } else {
        	break;
            }
        }
        if (app == null) {
            return false;      
        } else {
            assert g != null;
            g.apply(app);
            return true;
        }
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
            proverTaskObservers.get(i)
                .taskStarted(PROCESSING_STRATEGY, maxApplications);
        }
    }

    private synchronized void fireTaskProgress () {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            proverTaskObservers.get(i)
                .taskProgress(countApplied);
        }
    }

    private synchronized void fireTaskFinished (TaskFinishedInfo info) {
        for (int i = 0, sz = proverTaskObservers.size(); i<sz; i++) {
            proverTaskObservers.get(i).taskFinished(info);
        }
    }


    private void init(Proof proof, ListOfGoal goals, int maxSteps, long timeout) {
        this.proof = proof;
        maxApplications = maxSteps;
        this.timeout = timeout;
        countApplied = 0; 
        StrategySettings sSettings =medi.getProof().getSettings().getStrategySettings();
        if(!(sSettings.getStrategy().toString().equals(VBTStrategy.VBTStrategy))){
            if(usedCoalChooserOptionsKey.compareTo(sSettings.getActiveStrategyProperties().getProperty(StrategyProperties.GOALCHOOSER_OPTIONS_KEY))!=0){
            	usedCoalChooserOptionsKey = sSettings.getActiveStrategyProperties().getProperty(StrategyProperties.GOALCHOOSER_OPTIONS_KEY);
            	if(usedCoalChooserOptionsKey.equals(StrategyProperties.GOALCHOOSER_DEFAULT)){
            		medi.getProfile().setSelectedGoalChooserBuilder(DefaultGoalChooserBuilder.NAME);
            	}else if(usedCoalChooserOptionsKey.equals(StrategyProperties.GOALCHOOSER_DEPTH)){
            		medi.getProfile().setSelectedGoalChooserBuilder(DepthFirstGoalChooserBuilder.NAME);
            	}
            }
    	}else if(sSettings.getStrategy().toString().equals(VBTStrategy.VBTStrategy)){
    	    medi.getProfile().setSelectedGoalChooserBuilder(VBTStrategy.preferedGoalChooser);
    	}
	this.goalChooser = medi.getProfile().getSelectedGoalChooserBuilder().create();//Use this independently of StrategyProperties.GOALCHOOSER_OPTIONS_KEY

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
    


    public void start(Proof proof, ListOfGoal goals, int maxSteps, long timeout) {
        assert proof != null;
        init(proof, goals, maxSteps, timeout);

        worker = new AutoModeWorker();
        worker.start();
    }

    /**
     * Called by the "Stop" button, interrupts the worker thread 
     * which is running this.doWork().  Note that the doWork() 
     * method handles InterruptedExceptions cleanly.
     */
    public void stop () {
        if(worker!=null){
            worker.interrupt();
        }
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
            
            final Object result = get ();

            if ("Error".equals ( result )) {
                mediator ().startInterface ( true );                        
                mediator ().notify
                (new GeneralFailureEvent("An exception occurred during" 
                        + " strategy execution."));  
            } else {
                if (startedAsInteractive){
                    if (medi.getProof().getSettings().getStrategySettings()
			.getActiveStrategyProperties().getProperty(
			       StrategyProperties.STOPMODE_OPTIONS_KEY)
			.equals(StrategyProperties.STOPMODE_NONCLOSE)){
			Goal g = mediator().getSelectedGoal();
			mediator().startInterface(true);
			if(g != null) {
			    mediator().goalChosen(g);
			}
		    }else{
			mediator().startInterface(true);
		    }
		}
            }
            proof.addAutoModeTime(time);
            fireTaskFinished (new DefaultTaskFinishedInfo(ApplyStrategy.this, result, 
                    proof, time, 
                    countApplied, mediator().getNrGoalsClosedByAutoMode()));	  

            mediator().resetNrGoalsClosedByHeuristics();
            
            mediator().setInteractive( true );  
        }
    }
    
    private class ProofListener implements RuleAppListener {
    
	/** invoked when a rule has been applied */
	public void ruleApplied(ProofEvent e) {
            if (!isAutoModeActive() || e.getSource() != proof) return;            
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

    /**Used by, e.g., {@code InteractiveProver.clear()} in order to prevent memory leaking. 
     * When a proof obligation is abandoned all references to the proof must be reset.
     * @author gladisch */
    public void clear(){
        stop();
        proof = null;
        if(goalChooser!=null){
            goalChooser.init(null, SLListOfGoal.EMPTY_LIST);
        }
    }
}
