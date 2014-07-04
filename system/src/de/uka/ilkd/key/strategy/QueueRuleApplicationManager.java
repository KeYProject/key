// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableHeap;
import de.uka.ilkd.key.collection.ImmutableLeftistHeap;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.BooleanContainer;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.RuleAppIndex;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;


public class QueueRuleApplicationManager implements AutomatedRuleApplicationManager {

    /** The goal this manager belongs to */
    private Goal goal = null;

    /** The priority queue containing all possible next rule applications,
     * ordered by the costs the strategy object has assigned to them */
    private ImmutableHeap<RuleAppContainer> queue       = null;

    private ImmutableHeap<RuleAppContainer> secQueue    = null;
    
    /** rule apps that have been deferred during the last call
     * of <code>next</code>, but that could be still relevant */
    private ImmutableList<RuleAppContainer> workingList = null;

    private static final int PRIMARY_QUEUE   = 0;
    private static final int SECONDARY_QUEUE = 1;
    private static final int WORKING_LIST    = 2;

    private RuleApp nextRuleApp = null;
    private long nextRuleTime;
    private RuleAppCost nextRuleAppCost = null;

  
    public void setGoal ( Goal p_goal ) {
    	goal = p_goal;
    }


    /**
     * Clear the heap of applicable rules
     */
    public void clearCache () {
        queue       = null;
        secQueue    = null;
        workingList = null;
        TacletAppContainer.ifInstCache.reset(null);
        clearNextRuleApp ();
    }
    
    
    /**
     * Add all rules to the heap that are not reported via the <code>RuleListener</code>
     * connection
     */
    private void ensureQueueExists() {
        if ( queue != null ) return;

        if ( getGoal () == null ) {
            clearCache ();
            return;
        }

        queue = ImmutableLeftistHeap.<RuleAppContainer>nilHeap();
        secQueue = ImmutableLeftistHeap.<RuleAppContainer>nilHeap();
        workingList = ImmutableSLList.<RuleAppContainer>nil();

        // to support encapsulating rule managers (delegation, like in
        // <code>FocussedRuleApplicationManager</code>) the rule index
        // reports its contents to the rule manager of the goal, which is not
        // necessarily this object
        getGoal ().ruleAppIndex ()
                  .reportAutomatedRuleApps ( getGoal ().getRuleAppManager (),
                                             getServices () );
        //        printQueue(queue);
    }


    /**
     * Implementation of the method from <code>NewRuleListener</code>. The new
     * rule app is added to the heap
     */
    public void ruleAdded(RuleApp rule, PosInOccurrence pos) {
        //System.out.println ( "Rule added: " + rule + "\n");
        
        	//ensureQueueExists ();

        if ( queue == null )
            // then the heap has to be rebuilt completely anyway, and the new
            // rule app is not of interest for us
            return;
        final Iterator<RuleAppContainer> iterator = RuleAppContainer.createAppContainers
        	           ( rule, pos, getGoal (), getStrategy () ).iterator ();
        ensureQueueExists();
        push ( iterator,  PRIMARY_QUEUE );
    }


    /**
     * Add a number of new rule apps to the heap
     */
    private void push ( Iterator<RuleAppContainer> it, int target ) {
        while ( it.hasNext () ) {
            push ( it.next (), target );
        }
    }


    /**
     * Add a new rule app to the heap, provided that the rule app is not
     * infinitely expensive
     */
    private void push (RuleAppContainer c, int target) {
        if ( c.getCost () instanceof TopRuleAppCost )
            return;

        switch ( target ) {
        case PRIMARY_QUEUE:
            queue = queue.insert ( c );
            break;
        case SECONDARY_QUEUE:
            secQueue = secQueue.insert ( c );
            break;
        case WORKING_LIST:
            workingList = workingList.prepend(c);
            break;
        }
    }

    /**
     * @return the first applicable rule app, i.e. the least expensive element
     *         of the heap that is not obsolete and caches the result of this
     *         operation to save some time the next time the method
     *         nextAndCache() or next() is called. A call of next() empties the
     *         cache again.
     */
    public RuleApp peekNext() {
        ensureNextRuleAppExists ();
        return nextRuleApp;
    }

    public RuleAppCost peekCost () {
        ensureNextRuleAppExists ();
        return nextRuleAppCost;
    }

    /**
     * @return the first applicable rule app, i.e. the least expensive element
     * of the heap that is not obsolete
     */
    public RuleApp next() {
        ensureNextRuleAppExists ();
        
        final RuleApp res = nextRuleApp;
        clearNextRuleApp ();        
        
    	return res;
    }

    private void clearNextRuleApp () {
        nextRuleApp = null;
        nextRuleAppCost = null;
    }

    private void ensureNextRuleAppExists () {
        ensureQueueExists ();

        final long currentTime = getGoal ().getTime ();
        if ( currentTime != nextRuleTime ) {
            clearNextRuleApp ();
            nextRuleTime = currentTime;
        }
        
        if ( nextRuleApp != null ) return;
        
        final RuleAppIndex index = getGoal ().ruleAppIndex ();
        index.fillCache ();
        
//        printQueue(queue);
//        printQueue(secQueue);
            
        createFurtherApps ();
        
        ensureNextRuleAppExistsHelp ();
        
//        System.out.println("Queue size: " + queue.size());
//        System.out.println("Secondary queue size: " + secQueue.size());
//        System.out.println("Working list size: " + workingList.size());

        queue = queue.insert ( secQueue );
        secQueue = ImmutableLeftistHeap.<RuleAppContainer>nilHeap();        
    }


    
    private void ensureNextRuleAppExistsHelp () {
        final BooleanContainer secondaryQueueUsed = new BooleanContainer ();        
        clearNextRuleApp ();
        
        while ( nextRuleApp == null && ( !queue.isEmpty() || !secQueue.isEmpty() ) ) {
            final RuleAppContainer c = getMinRuleApp ( secondaryQueueUsed );
//            printContainer ( "considering rule ", c );

            nextRuleApp = c.completeRuleApp(getGoal(), getStrategy());
            
            if(nextRuleApp == null && c instanceof BuiltInRuleAppContainer) {
        	//XXX
	    } else if ( nextRuleApp == null ) {
                if ( !secondaryQueueUsed.val () )
                    createFurtherRuleApps ( c, true );
                else
                    push ( c, WORKING_LIST );
            } else {
                nextRuleAppCost = c.getCost ();

                // the found rule app will be re-evaluated when calling
                // <code>next()</code> the next time; all other considered rule
                // apps can be put into the primary queue immediately
                queue = queue.insert ( workingList.iterator () );
                workingList = ImmutableSLList.<RuleAppContainer>nil();
                push ( c, WORKING_LIST );
            }
            
//            if (res != null) {
//                printContainer ( "selected rule ", c );
//            }
        }
    }

    private RuleAppContainer getMinRuleApp (BooleanContainer usedSecondary) {
        if ( queue.isEmpty () ) {
            usedSecondary.setVal ( true );
            final RuleAppContainer c = secQueue.findMin ();
            secQueue = secQueue.deleteMin ();
            return c;
        }

        if ( secQueue.isEmpty () ) {
            usedSecondary.setVal ( false );
            final RuleAppContainer c = queue.findMin ();
            queue = queue.deleteMin ();
            return c;
        }

        final RuleAppContainer priC = queue.findMin ();
        final RuleAppContainer secC = secQueue.findMin ();

        usedSecondary.setVal ( priC.compareTo ( secC ) > 0 );

        if ( usedSecondary.val () ) {
            secQueue = secQueue.deleteMin ();
            return secC;
        } else {
            queue = queue.deleteMin ();
            return priC;
        }
    }
    
    /**
     * Call the method <code>createFurtherApps</code> for all elements of
     * the list <code>consideredRecently</code>, and clear the list. The new
     * rule apps are added to the heap
     */
    private void createFurtherApps () {
    	final Iterator<RuleAppContainer> it = workingList.iterator();
    	workingList = ImmutableSLList.<RuleAppContainer>nil();
    
        while ( it.hasNext() )
            createFurtherRuleApps ( it.next (), true );
    }


    private void createFurtherRuleApps (RuleAppContainer app, boolean secondary) {
        push ( app.createFurtherApps ( getGoal (), getStrategy () ).iterator (),
               secondary ? SECONDARY_QUEUE : PRIMARY_QUEUE );
    }

    
    /**
     * The goal this manager belongs to
     */
    private Goal getGoal() {
        return goal;
    }

    private Services getServices() {
	return getProof ().getServices ();
    }

    private Proof getProof() {
	return getGoal ().proof ();
    }

    private Strategy getStrategy () {
    	return getGoal().getGoalStrategy();
    }

    public AutomatedRuleApplicationManager copy () {
    	return (AutomatedRuleApplicationManager)clone ();
    }

    public Object clone () {
    	QueueRuleApplicationManager res = new QueueRuleApplicationManager ();
    	res.queue                   = queue;
        res.secQueue                = secQueue;
    	res.workingList             = workingList;
    	return res;
    }
    
    void printQueue(ImmutableHeap<RuleAppContainer> p_queue) {
        Iterator<RuleAppContainer> it = p_queue.sortedIterator();
        
        System.out.println("---- start of queue ----");
        
        int n = 0;
        while (it.hasNext ()) {
            n++;
            final RuleAppContainer container = it.next ();

            final String prefix = n + ") ";
            printContainer ( prefix, container );
        }
        
        System.out.println("---- end of queue ----");
    }


    private void printContainer ( String           prefix,
            			  RuleAppContainer container ) {
        final RuleApp ruleApp = container.getRuleApp ();
        String message = prefix + ruleApp.rule ().name ()
                + " with cost " + container.getCost ();
        
        if ( ruleApp instanceof TacletApp ) {
            TacletApp tacletApp = (TacletApp) ruleApp;
            if ( !tacletApp.ifInstsComplete() ) {
                message = message + " (unmatched if-formulas)";
            }
            if ( !tacletApp.complete () ) {
                message = message + " (incomplete)";
            }
        }
        
        System.out.println ( message );
    }


    /**
     * this rule app manager has no manager to delegate to
     * but is the "base" manager.
     */
    public AutomatedRuleApplicationManager getDelegate() {
        return null;
    }
}