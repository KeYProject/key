// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;


/** the class manages the available TacletApps. This index has to be
 * used if one wants to ask for the available taclet application at a
 * specific position (or the whole sequent if taclet is a nofind
 * rule). This means all taclet applications that have a position
 * information are managed by this index. For all others the class
 * TacletIndex is used. This index uses also the TacletIndex to
 * calculate new TacletApps.
 */

public class TacletAppIndex  {

    private final TacletIndex         tacletIndex;

    private SemisequentTacletAppIndex antecIndex;
    private SemisequentTacletAppIndex succIndex;

    private TermTacletAppIndexCacheSet indexCaches;    

    private Goal                      goal;
    
    /**
     * Object to which the appearance of new taclet apps is reported
     */
    private NewRuleListener           newRuleListener =
        NullNewRuleListener.INSTANCE;

    /**
     * Filter that is used to restrict the set of taclets that are considered as
     * possible members of this index. This is used to distinguish between
     * <code>TacletAppIndex</code> s exclusively for automatic or interactive
     * taclets.
     */
    private RuleFilter                ruleFilter;
    
    /** The sequent with the formulas for which taclet indices are hold by
     * this object. Invariant: <code>seq != null</code> implies that the
     * indices <code>antecIndex</code>, <code>succIndex</code> are up to date
     * for the sequent <code>seq</code> */
    private Sequent                   seq;

    public TacletAppIndex(TacletIndex tacletIndex) {
        this ( tacletIndex,
               null, null, null, null, TacletFilter.TRUE,
               new TermTacletAppIndexCacheSet () );
    }

    private TacletAppIndex ( TacletIndex               tacletIndex,
                             SemisequentTacletAppIndex antecIndex,
                             SemisequentTacletAppIndex succIndex,
                             Goal                      goal,
                             Sequent                   seq,
                             RuleFilter                ruleFilter,
                             TermTacletAppIndexCacheSet indexCaches ) {
        this.tacletIndex = tacletIndex;
        this.antecIndex  = antecIndex;
        this.succIndex   = succIndex;
        this.goal        = goal;
        this.seq         = seq;
        this.ruleFilter  = ruleFilter;
        this.indexCaches = indexCaches;
    }

    public void setNewRuleListener ( NewRuleListener p_newRuleListener ) {
    	newRuleListener = p_newRuleListener;
    }

    private NewRuleListener getNewRulePropagator () {
    	return newRuleListener;
    }

    public void setRuleFilter(RuleFilter p_ruleFilter) {
        if ( p_ruleFilter != ruleFilter ) {
            ruleFilter = p_ruleFilter;
            clearAndDetachCache ();
        }
    }

    private RuleFilter getRuleFilter() {
        return ruleFilter;
    }

    /**
     * returns a new TacletAppIndex with a given TacletIndex
     */
    TacletAppIndex copyWithTacletIndex(TacletIndex p_tacletIndex) {
        return new TacletAppIndex ( p_tacletIndex, antecIndex, succIndex,
                                    getGoal (), getSequent (), ruleFilter,
                                    indexCaches );
    }

    /**
     * Set the goal association of this index to the given object
     * <code>p_goal</code>. If the sequent of the new goal differs from the
     * former one (attribute <code>seq</code>), the index will be rebuilt as
     * soon as data is requested from it.
     */
    public void setup(Goal p_goal) {
        goal = p_goal;
    }

    /**
     * Delete all cached information about taclet apps. This also makes the
     * index cache of this index independent from the caches of other indexes
     * (expensive)
     */
    public void clearAndDetachCache () {
        clearIndexes ();
        createNewIndexCache ();
    }

    public void clearIndexes () {
        seq        = null; // This leads to a delayed rebuild
        antecIndex = null;
        succIndex  = null;
    }

    private void createNewIndexCache() {
        indexCaches = new TermTacletAppIndexCacheSet ();
        if ( antecIndex != null ) antecIndex.setIndexCache ( indexCaches );
        if ( succIndex != null ) succIndex.setIndexCache ( indexCaches );
    }
    
    /**
     * Forces all delayed computations to be performed, so that
     * the cache is fully up-to-date (NewRuleListener gets informed)
     */
    public void fillCache() {
        ensureIndicesExist ();
    }

    private void createAllFromGoal() {
        this.seq = getNode ().sequent ();

        antecIndex = new SemisequentTacletAppIndex ( getSequent (), true,
                                                     getServices (),
                                                     getUserConstraint (),
                                                     tacletIndex (),
                                                     getNewRulePropagator (),
                                                     getRuleFilter (),
                                                     indexCaches );
        succIndex = new SemisequentTacletAppIndex ( getSequent (), false,
                                                    getServices (),
                                                    getUserConstraint (),
                                                    tacletIndex (),
                                                    getNewRulePropagator (),
                                                    getRuleFilter (),
                                                    indexCaches );
    }

    private void ensureIndicesExist () {
    	Debug.assertFalse ( getGoal () == null,
    	                    "TacletAppIndex does not know to which goal it " +
                            "refers" );

    	if ( !isUpToDateForGoal() )
    	    // Indices are not up to date
            createAllFromGoal ();	    
    }

    /**
     * @return true iff this index currently is up to date with respect to the
     * sequent of the associated goal; this does not detect other modifications
     * like an altered user constraint
     */
    private boolean isUpToDateForGoal() {
        return getGoal () != null && getSequent() == getNode().sequent();
    }

    private SemisequentTacletAppIndex getIndex(PosInOccurrence pos) {
        ensureIndicesExist ();
        return pos.isInAntec () ? antecIndex : succIndex;
    }

    private ListOfTacletApp getFindTacletWithPos ( PosInOccurrence pos,
                                                   TacletFilter    filter,
                                                   Services        services, 
                                                   Constraint      userConstraint ) {
        Debug.assertFalse ( pos == null );
        ListOfNoPosTacletApp tacletInsts = getFindTaclet ( pos, filter,
                                                           services,
                                                           userConstraint );
        return createTacletApps ( tacletInsts, pos, services );
    }

     
    /** returns the set of rule applications
     * at the given position of the given sequent.
     * @param pos the PosInOccurrence to focus
     */
    public ListOfTacletApp getTacletAppAt(PosInOccurrence pos,
                                          TacletFilter    filter,
                                          Services        services,
                                          Constraint      userConstraint) {
        ListOfTacletApp sal = getFindTacletWithPos ( pos, filter, services,
                                                     userConstraint );
        return prepend ( sal,
                         getNoFindTaclet ( filter, services, userConstraint ) );
    }
    
    /** creates TacletApps out of each single NoPosTacletApp object
     * @param tacletInsts the list of NoPosTacletApps the TacletApps are to
     * be created from
     * @param pos the PosInOccurrence to focus
     * @return list of all created TacletApps
     */
    static ListOfTacletApp createTacletApps(ListOfNoPosTacletApp tacletInsts,
                                            PosInOccurrence pos,
                                            Services services) {
        ListOfTacletApp result = SLListOfTacletApp.EMPTY_LIST;
        IteratorOfNoPosTacletApp it = tacletInsts.iterator ();
        while ( it.hasNext () ) {
            NoPosTacletApp tacletApp = it.next ();
            if ( tacletApp.taclet () instanceof FindTaclet ) {
                PosTacletApp newTacletApp = tacletApp.setPosInOccurrence ( pos, services );
                if ( newTacletApp != null ) {
                    result = result.prepend ( newTacletApp );
                }
            } else {
                result = result.prepend ( tacletApp );
            }
        }
        return result;
    }
    
    static TacletApp createTacletApp(NoPosTacletApp tacletApp,
                                     PosInOccurrence pos,
                                     Services services) {
        if ( tacletApp.taclet () instanceof FindTaclet ) {
            PosTacletApp newTacletApp = tacletApp.setPosInOccurrence ( pos, services );
            if ( newTacletApp != null ) {
                return newTacletApp;
            } else {
                return null;
            }
        } else {
            return tacletApp;
        }
    }

    /** 
     * collects all NoFindTacletInstantiations
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    public ListOfNoPosTacletApp getNoFindTaclet(TacletFilter filter,
                                                Services services,
                                                Constraint userConstraint) {
        RuleFilter effectiveFilter = new AndRuleFilter ( filter, ruleFilter );
        return tacletIndex ().getNoFindTaclet ( effectiveFilter, services,
                                                userConstraint );
    }

    /** 
     * collects all RewriteTacletInstantiations in a subterm of the
     * constrainedFormula described by a
     * PosInOccurrence
     * @param pos the PosInOccurrence to focus 
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    public ListOfNoPosTacletApp getRewriteTaclet(PosInOccurrence pos, 
                                                 TacletFilter    filter,
                                                 Services        services,
                                                 Constraint      userConstraint) { 

        final IteratorOfNoPosTacletApp it =
            getFindTaclet ( pos, filter, services, userConstraint ).iterator();

        ListOfNoPosTacletApp result = SLListOfNoPosTacletApp.EMPTY_LIST;

        while ( it.hasNext () ) {
            final NoPosTacletApp tacletApp = it.next ();
            if ( tacletApp.taclet () instanceof RewriteTaclet )
                result = result.prepend ( tacletApp );
        }

        return result;
    }

    /** 
     * collects all FindTaclets with instantiations and position
     * @param pos the PosInOccurrence to focus
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    public ListOfNoPosTacletApp getFindTaclet(PosInOccurrence pos,
                                              TacletFilter    filter,
                                              Services        services,
                                              Constraint      userConstraint) { 
        return getIndex ( pos ).getTacletAppAt ( pos, filter );
    }


    /**
     * returns the rule applications at the given PosInOccurrence and at all
     * Positions below this. The method calls getTacletAppAt for all the
     * Positions below.
     * @param pos the position where to start from
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return the possible rule applications 
     */
    public ListOfTacletApp getTacletAppAtAndBelow(PosInOccurrence pos,
                                                  TacletFilter    filter,
                                                  Services        services,
                                                  Constraint      userConstraint) {
        final ListOfTacletApp findTaclets =
            getIndex ( pos ).getTacletAppAtAndBelow ( pos, filter, services );
        return prepend ( findTaclets,
                         getNoFindTaclet ( filter, services, userConstraint ) );
    }

    /** 
     * called if a formula has been replaced
     * @param sci SequentChangeInfo describing the change of the sequent 
     */  
    public void sequentChanged ( Goal goal, SequentChangeInfo sci ) {
    	if ( sci.getOriginalSequent() != getSequent() )
    	    // we are not up to date and have to rebuild everything (lazy)
    	    clearIndexes();
    	else
    	    updateIndices ( sci );
    }

    private void updateIndices(SequentChangeInfo sci) {
        seq = sci.sequent ();

        antecIndex = antecIndex.sequentChanged ( sci, getServices (),
                                                 getUserConstraint (),
                                                 tacletIndex (),
                                                 getNewRulePropagator () );

        succIndex = succIndex.sequentChanged ( sci, getServices (),
                                               getUserConstraint (),
                                               tacletIndex (),
                                               getNewRulePropagator () );
    }

    /**
     * updates the internal caches after a new Taclet with instantiation
     * information has been added to the TacletIndex.
     * @param tacletApp the partially instantiated Taclet to add
     */
    public void addedNoPosTacletApp(NoPosTacletApp tacletApp) {
        if ( indexCaches.isRelevantTaclet ( tacletApp.taclet () ) ) {
            // we must flush the index cache, and we must no longer use a cache
            // that we share with other instances of <code>TacletAppIndex</code>
            // (that maybe live of different goals)
            createNewIndexCache ();            
        }
        
        if ( !isUpToDateForGoal () ) {
            // we are not up to date and have to rebuild everything (lazy)
            clearIndexes ();
            return;
        }
            
    	if ( tacletApp.taclet() instanceof NoFindTaclet ) {
            if ( ruleFilter.filter ( tacletApp.taclet() ) )
    	       getNewRulePropagator().ruleAdded(tacletApp, null);
    	    return;
    	}
    	
    	final SetRuleFilter newTaclets = new SetRuleFilter ();
        newTaclets.addRuleToSet ( tacletApp.taclet () );

        antecIndex = antecIndex.addTaclets ( newTaclets, getSequent (),
                                             getServices (),
                                             getUserConstraint (),
                                             tacletIndex (),
                                             getNewRulePropagator () );
        succIndex = succIndex.addTaclets ( newTaclets, getSequent (),
                                           getServices (),
                                           getUserConstraint (),
                                           tacletIndex (),
                                           getNewRulePropagator () );
    }

    /**
     * updates the internal caches after a Taclet with instantiation
     * information has been removed from the TacletIndex.
     * @param tacletApp the partially instantiated Taclet to remove
     */
    public void removedNoPosTacletApp(NoPosTacletApp tacletApp) {
        if ( indexCaches.isRelevantTaclet ( tacletApp.taclet () ) ) {
            // we must flush the index cache, and we must no longer use a cache
            // that we share with other instances of <code>TacletAppIndex</code>
            // (that maybe live of different goals)
            clearAndDetachCache ();
        } else {
            clearIndexes ();
        }
    }

    public String toString() {
        return "TacletAppIndex with indexing, getting Taclets from"
               + " TacletIndex " + tacletIndex ();
    }

    // helper because ListOfNoPosTacletApp is no ListOfTacletApp
    private static ListOfTacletApp prepend(ListOfTacletApp l1,
                                           ListOfNoPosTacletApp l2) {
        IteratorOfNoPosTacletApp it = l2.iterator ();
        while ( it.hasNext () ) {
            l1 = l1.prepend ( it.next () );
        }
        return l1;
    }

    private Goal getGoal() {
        return goal;
    }

    private Sequent getSequent() {
        return seq;
    }

    private Constraint getUserConstraint() {
        return getProof ().getUserConstraint ().getConstraint ();
    }

    private Services getServices() {
        return getProof ().getServices ();
    }

    private Proof getProof() {
        return getNode ().proof ();
    }

    private Node getNode() {
        return getGoal ().node ();
    }

    /**
     * returns the Taclet index for this ruleAppIndex. 
     */
    public TacletIndex tacletIndex() {
        return tacletIndex;
    }
    
    /**
     * Reports all cached rule apps.
     * Calls ruleAdded on the given NewRuleListener for
     * every cached taclet app.
     */
    public void reportRuleApps (NewRuleListener l,
                                Services services,
                                Constraint userConstraint) {
        if ( antecIndex != null ) antecIndex.reportRuleApps ( l );
        if ( succIndex != null ) succIndex.reportRuleApps ( l );

        final IteratorOfNoPosTacletApp it =
            getNoFindTaclet ( TacletFilter.TRUE,
                              services,
                              userConstraint ).iterator ();
        while ( it.hasNext () )
            l.ruleAdded ( it.next (), null );
    }
}
