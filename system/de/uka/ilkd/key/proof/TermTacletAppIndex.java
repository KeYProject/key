// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.pp.ConstraintSequentPrintFilter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;

/**
 * Class whose objects represent an index of taclet apps for one particular
 * position within a formula, and that also contain references to the indices of
 * direct subformulas
 */
public class TermTacletAppIndex {
    /** the term for which NoPosTacletApps are kept in this index node */
    private final Term term;
    /** NoPosTacletApps for this term */
    private final ListOfNoPosTacletApp localTacletApps;
    /** indices for subterms */
    private final ListOfTermTacletAppIndex subtermIndices;
    /** the constraint that is used to extend the considered term below
     *  metavariables */
    private final Constraint displayConstraint;
    /** */
    private final RuleFilter ruleFilter;

    /**
     * Create a TermTacletAppIndex
     */
    private TermTacletAppIndex( Term term,
                                ListOfNoPosTacletApp localTacletApps,
                                ListOfTermTacletAppIndex subtermIndices,
                                Constraint displayConstraint,
                                RuleFilter ruleFilter ) {
        this.term              = term;
        this.subtermIndices    = subtermIndices;
        this.localTacletApps   = localTacletApps;
        this.displayConstraint = displayConstraint;
        this.ruleFilter        = ruleFilter;
    }


    private TermTacletAppIndex getSubIndex ( int subterm ) {
        return subtermIndices.take ( subterm ).head ();
    }


    /** 
     * collects all RewriteTacletInstantiations for the given
     * heuristics in a subterm of the constrainedFormula described by a
     * PosInOccurrence
     * @param pos the PosInOccurrence to focus 
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ListOfNoPosTacletApp getRewriteTaclet(PosInOccurrence pos,
                                                         RuleFilter      filter,
                                                         Services        services,
                                                         Constraint      userConstraint,
                                                         TacletIndex     tacletIndex) { 

        ListOfNoPosTacletApp result = SLListOfNoPosTacletApp.EMPTY_LIST;

        Constraint c = pos.constrainedFormula().constraint();

        if ( pos.termBelowMetavariable () != null ) {
            c = c.unify ( pos.constrainedFormula ().formula ().subAt ( pos.posInTerm () ),
                          pos.termBelowMetavariable (), services );
            if ( !c.isSatisfiable () ) return SLListOfNoPosTacletApp.EMPTY_LIST;
        }
		
        final IteratorOfNoPosTacletApp rewriteIterator =
            tacletIndex.getRewriteTaclet ( pos, c, filter, services,
                                           userConstraint ).iterator();

        while ( rewriteIterator.hasNext () ) {
            NoPosTacletApp tacletApp = rewriteIterator.next ();
            result = result.prepend ( tacletApp );
        }
        
        return result;
    }
  
    /** 
     * collects all FindTaclets with instantiations for the given
     * heuristics and position
     * @param pos the PosInOccurrence to focus
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ListOfNoPosTacletApp getFindTaclet(PosInOccurrence pos,
                                                      RuleFilter      filter,
                                                      Services        services,
                                                      Constraint      userConstraint,
                                                      TacletIndex     tacletIndex) { 
        ListOfNoPosTacletApp tacletInsts = SLListOfNoPosTacletApp.EMPTY_LIST;
        if ( pos.isTopLevel () ) {
            if ( pos.isInAntec () ) {
                tacletInsts =
                    tacletInsts.prepend ( antecTaclet ( pos, filter, services,
                                                        userConstraint,
                                                        tacletIndex ) );
            } else {
                tacletInsts =
                    tacletInsts.prepend ( succTaclet ( pos, filter, services,
                                                       userConstraint,
                                                       tacletIndex ) );
            }
        } else {
            tacletInsts =
                tacletInsts.prepend ( getRewriteTaclet ( pos, filter, services,
                                                         userConstraint,
                                                         tacletIndex ) );
        }
        return tacletInsts;
    }


    /** 
     * collects all AntecedentTaclet instantiations for the given
     * heuristics and ConstrainedFormula
     * @param pos the PosInOccurrence of the ConstrainedFormula 
     *  the taclets have to be connected to 
     * (pos must point to the top level formula, i.e. <tt>pos.isTopLevel()</tt> must be true)     
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ListOfNoPosTacletApp antecTaclet(PosInOccurrence pos,
                                                    RuleFilter filter,
                                                    Services services,
                                                    Constraint userConstraint,
                                                    TacletIndex tacletIndex) {
        return tacletIndex.getAntecedentTaclet ( pos, filter, services,
                                                 userConstraint );
    }
    
    /** 
     * collects all SuccedentTaclet instantiations for the given
     * heuristics and ConstrainedFormula
     * @param pos the PosInOccurrence of the ConstrainedFormula 
     *  the taclets have to be connected to 
     * (pos must point to the top level formula, 
     * i.e. <tt>pos.isTopLevel()</tt> must be true)     
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ListOfNoPosTacletApp succTaclet(PosInOccurrence pos,
                                                   RuleFilter filter,
                                                   Services services,
                                                   Constraint userConstraint,
                                                   TacletIndex tacletIndex) {
        return tacletIndex.getSuccedentTaclet ( pos, filter, services,
                                                userConstraint );
    }


    /**
     * Check whether the given term is a metavariable, and replace it
     * with a concrete term provided that such a term is determined by
     * the user constraint
     * @return A <code>PosInOccurrence</code> object in which
     * eventually the metavariable has been replaced with a term as
     * given by the user constraint. In any case the object points to
     * the same position of a term as the <code>pos</code> parameter
     */
    private static PosInOccurrence
                   handleDisplayConstraint(PosInOccurrence pos,
                                           Constraint displayConstraint) {

        final Term localTerm = pos.subTerm ();

        final Operator op = localTerm.op ();
        if ( op instanceof Metavariable ) {
            if ( pos.termBelowMetavariable () == null ) {
                final Term metaTerm =
                    displayConstraint.getInstantiation ( (Metavariable)op );
                if ( metaTerm.op () != op )
                    return pos.setTermBelowMetavariable ( metaTerm );
            }
        }

        return pos;
    }


    /**
     * Descend and create indices for each of the direct subterms of
     * the given term
     * @param pos pointer to the term/formula for whose subterms
     * indices are to be created
     * @return list of the index objects
     */
    private static ListOfTermTacletAppIndex
                   createSubIndices (PosInOccurrence pos,
                                     Services        services,
                                     Constraint      userConstraint,
                                     Constraint      displayConstraint,
                                     TacletIndex     tacletIndex,
                                     NewRuleListener listener,
                                     RuleFilter      filter,
                                     ITermTacletAppIndexCache indexCache) {
        ListOfTermTacletAppIndex result = SLListOfTermTacletAppIndex.EMPTY_LIST;
        final Term localTerm = pos.subTerm ();
    
        int i = localTerm.arity();

        while ( i-- != 0 )
            result = result.prepend ( createHelp ( pos.down(i),
                                                   services,
                                                   userConstraint,
                                                   displayConstraint,
                                                   tacletIndex,
                                                   listener,
                                                   filter,
                                                   indexCache.descend ( localTerm, i ) ) );

        return result;
    }


    /**
     * Create an index for the given term
     * 
     * @param pos
     *            Pointer to the term/formula for which an index is to be
     *            created. <code>pos</code> has to be a top-level term
     *            position
     * @return the index object
     */
    public static TermTacletAppIndex create(PosInOccurrence pos,
                                            Services        services,
                                            Constraint      userConstraint,
                                            TacletIndex     tacletIndex,
                                            NewRuleListener listener,
                                            RuleFilter      filter,
                                            TermTacletAppIndexCacheSet indexCaches) {
        Debug.assertTrue ( pos.isTopLevel (),
                           "Someone tried to create a term index for a real " +
                           "subterm" );
	    // This depends on the active implementation of
        // <code>SequentPrintFilter</code>, and has to be compatible
        // with the displayed sequent
        final Constraint localDisplayConstraint =
	             ConstraintSequentPrintFilter.determineDisplayConstraint
	             ( pos.constrainedFormula (), userConstraint );

        final ITermTacletAppIndexCache indexCache =
            determineIndexCache ( pos, indexCaches, localDisplayConstraint );
        
        return createHelp ( pos, services, userConstraint,
                            localDisplayConstraint, tacletIndex, listener,
                            filter, indexCache );
    }

    private static ITermTacletAppIndexCache
                   determineIndexCache(PosInOccurrence pos,
                                       TermTacletAppIndexCacheSet indexCaches,
                                       final Constraint localDisplayConstraint) {
        if ( !localDisplayConstraint.isBottom () )
            return indexCaches.getNoCache ();
        
        if ( pos.isInAntec () )
            return indexCaches.getAntecCache ();
        else
            return indexCaches.getSuccCache ();
    }


    private static TermTacletAppIndex createHelp(PosInOccurrence pos,
                                                 Services        services,
                                                 Constraint      userConstraint,
                                                 Constraint      displayConstraint,
                                                 TacletIndex     tacletIndex,
                                                 NewRuleListener listener,
                                                 RuleFilter      filter,
                                                 ITermTacletAppIndexCache indexCache) {
        pos = handleDisplayConstraint ( pos, displayConstraint );
        final Term localTerm = pos.subTerm ();

        final TermTacletAppIndex cached = indexCache.getIndexForTerm ( localTerm );
        if ( cached != null ) {
            cached.reportTacletApps ( pos, listener );
            return cached;
        }
        
        final ListOfNoPosTacletApp localApps = getFindTaclet ( pos, filter,
                                                               services,
                                                               userConstraint,
                                                               tacletIndex );

        final ListOfTermTacletAppIndex subIndices =
            createSubIndices ( pos, services, userConstraint,
                               displayConstraint, tacletIndex, listener,
                               filter, indexCache );

        fireRulesAdded ( listener, localApps, pos );

        final TermTacletAppIndex res = new TermTacletAppIndex ( localTerm,
                                                                localApps,
                                                                subIndices,
                                                                displayConstraint,
                                                                filter );
        indexCache.putIndexForTerm ( localTerm, res );

        return res;
    }


    /**
     * Create a new tree of indices that additionally contain the taclets that
     * are selected by <code>filter</code>
     * @param filter The taclets that are supposed to be added
     * @param pos Pointer to the term/formula for which an index is to
     * be created. <code>pos</code> has to be a top-level term
     * position
     * @return the index object
     */
    public TermTacletAppIndex addTaclets(RuleFilter      filter,
                                         PosInOccurrence pos,
                                         Services        services,
                                         Constraint      userConstraint,
                                         TacletIndex     tacletIndex,
                                         NewRuleListener listener) {
        RuleFilter effectiveFilter = new AndRuleFilter ( filter, ruleFilter );

        return addTacletsHelp ( effectiveFilter, pos, services, userConstraint,
                                tacletIndex, listener );
    }

    private TermTacletAppIndex addTacletsHelp(RuleFilter      filter,
                                              PosInOccurrence pos,
                                              Services        services,
                                              Constraint      userConstraint,
                                              TacletIndex     tacletIndex,
                                              NewRuleListener listener) {
        pos = handleDisplayConstraint ( pos, displayConstraint );

        final ListOfTermTacletAppIndex newSubIndices =
            addTacletsSubIndices ( filter, pos, services, userConstraint,
                                   tacletIndex, listener );
	
        final ListOfNoPosTacletApp additionalApps =
            getFindTaclet ( pos, filter, services, userConstraint, tacletIndex );

        fireRulesAdded ( listener, additionalApps, pos );
			    
        return new TermTacletAppIndex ( term,
                                        localTacletApps.prepend ( additionalApps ),
                                        newSubIndices,
                                        displayConstraint,
                                        ruleFilter );
    }


    private ListOfTermTacletAppIndex addTacletsSubIndices( RuleFilter      filter,
                                                           PosInOccurrence pos,
                                                           Services        services,
                                                           Constraint      userConstraint,
                                                           TacletIndex     tacletIndex,
                                                           NewRuleListener listener ) {
        ListOfTermTacletAppIndex result = SLListOfTermTacletAppIndex.EMPTY_LIST;
        final IteratorOfTermTacletAppIndex subIt = subtermIndices.iterator();
        
        int i = 0;
        while ( subIt.hasNext () ) {
            final TermTacletAppIndex oldSubIndex = subIt.next ();
            final TermTacletAppIndex newSubIndex =
                oldSubIndex.addTacletsHelp ( filter, pos.down ( i ), services,
                                             userConstraint, tacletIndex,
                                             listener );
            result = result.append ( newSubIndex );
            ++i;
        }
        
        return result;
    }


    /**
     * Recursively update the term index, starting at <code>this</code> and
     * descending along the given path iterator to the term position below which
     * a modification was performed
     * @param pathToModification an iterator that walks from the root of the
     * formula to the position of modification
     * @return the updated TermTacletAppIndex
     */
    private TermTacletAppIndex updateHelp(PIOPathIterator pathToModification,
                                          Services services,
                                          Constraint userConstraint,
                                          TacletIndex tacletIndex,
                                          NewRuleListener listener,
                                          ITermTacletAppIndexCache indexCache) {

        pathToModification.next ();

        // Below the position of modification everything has to be rebuilt
        final boolean completeRebuild = !pathToModification.hasNext ();
        final PosInOccurrence pos = pathToModification.getPosInOccurrence ();

        if ( completeRebuild )
            return updateCompleteRebuild ( pos, services, userConstraint,
                                           tacletIndex, listener, indexCache );

        final Term newTerm = pathToModification.getSubTerm ();

        final TermTacletAppIndex cached = indexCache.getIndexForTerm ( newTerm );
        if ( cached != null ) {
            cached.reportTacletApps ( pathToModification, listener );
            return cached;
        }

        final ListOfTermTacletAppIndex newSubIndices =
            updateSubIndexes ( pathToModification, services, userConstraint,
                               tacletIndex, listener, indexCache );
            
        final TermTacletAppIndex res =
            updateLocalApps ( pos, newTerm, services, userConstraint,
                              tacletIndex, listener, newSubIndices );
        
        indexCache.putIndexForTerm ( newTerm, res );
        return res;
    }


    private TermTacletAppIndex updateCompleteRebuild(PosInOccurrence pos,
                                                     Services services,
                                                     Constraint userConstraint,
                                                     TacletIndex tacletIndex,
                                                     NewRuleListener listener,
                                                     ITermTacletAppIndexCache indexCache) {
        final Term newTerm = pos.subTerm ();
        final Operator newOp = newTerm.op ();
        
        if ( newOp instanceof Modality && newOp == term.op ()
             && newTerm.sub ( 0 ).equals ( term.sub ( 0 ) ) ) {
            // only the program within a modal operator has changed, but not the
            // formula after the modal operator. in this case, the formula after
            // the modality does not have to be rematched. also consider
            // <code>FindTacletAppContainer.independentSubformulas</code>
            return updateLocalApps ( pos, newTerm, services, userConstraint,
                                     tacletIndex, listener, subtermIndices );
        }
        
        return createHelp ( pos, services, userConstraint, displayConstraint,
                            tacletIndex, listener, ruleFilter, indexCache );
    }


    private TermTacletAppIndex updateLocalApps(PosInOccurrence pos,
                                               Term newSubterm,
                                               Services services,
                                               Constraint userConstraint,
                                               TacletIndex tacletIndex,
                                               NewRuleListener listener,
                                               ListOfTermTacletAppIndex newSubIndices) {
        final ListOfNoPosTacletApp localApps = getFindTaclet ( pos, ruleFilter,
                                                               services,
                                                               userConstraint,
                                                               tacletIndex );

        fireRulesAdded ( listener, localApps, pos );

        return new TermTacletAppIndex ( newSubterm, localApps, newSubIndices,
                                        displayConstraint, ruleFilter );
    }


    private ListOfTermTacletAppIndex
               updateSubIndexes(PIOPathIterator pathToModification,
                                Services services,
                                Constraint userConstraint,
                                TacletIndex tacletIndex,
                                NewRuleListener listener,
                                ITermTacletAppIndexCache indexCache) {
        ListOfTermTacletAppIndex newSubIndices = subtermIndices;
        
        final Term newTerm = pathToModification.getSubTerm ();
        final int child = pathToModification.getChild ();
        
        if ( newTerm.op () instanceof IUpdateOperator ) {
            final int targetPos = ( (IUpdateOperator)newTerm.op () ).targetPos ();
            if ( child != targetPos ) {
                newSubIndices =
                    updateIUpdateTarget ( newSubIndices,
                                          targetPos,
                                          pathToModification.getPosInOccurrence ()
                                                            .down ( targetPos ),
                                          services,
                                          userConstraint,
                                          tacletIndex,
                                          listener,
                                          indexCache.descend ( newTerm, targetPos ) );
            }
        }
        
        return updateOneSubIndex ( newSubIndices, pathToModification, services,
                                   userConstraint, tacletIndex, listener,
                                   indexCache.descend ( newTerm, child ) );
    }

    
    /**
     * Update the target formula/term of an update (which has position
     * <code>subtermPos</code> in the complete formula). This is necessary
     * whenever a part of the update has changed, because this also changes the
     * update context of taclet apps in the target.
     */
    private ListOfTermTacletAppIndex
                 updateIUpdateTarget ( ListOfTermTacletAppIndex oldSubindices,
                                       int             updateTarget,
                                       PosInOccurrence targetPos,
                                       Services        services,
                                       Constraint      userConstraint,
                                       TacletIndex     tacletIndex,
                                       NewRuleListener listener,
                                       ITermTacletAppIndexCache indexCache ) {

        ListOfTermTacletAppIndex subindices = oldSubindices.take ( updateTarget );                              
        final TermTacletAppIndex toBeRemoved = subindices.head ();
        final Term targetTerm = toBeRemoved.term;
        subindices = subindices.tail ();

        final TermTacletAppIndex newSubIndex;
        
        if ( targetTerm.op() instanceof Modality ) {
            // it is enough to update the local rule apps of the target, because
            // all apps below the modality have to be independent of update
            // contexts anyway. this is a very common case, because updates
            // usually occur in front of programs
            newSubIndex = toBeRemoved.updateLocalApps ( targetPos, targetTerm,
                                                        services, userConstraint,
                                                        tacletIndex, listener,
                                                        toBeRemoved.subtermIndices );
        } else {
            // the target is updated completely otherwise
            newSubIndex = createHelp ( targetPos, services, userConstraint,
                                       toBeRemoved.displayConstraint,
                                       tacletIndex, listener,
                                       toBeRemoved.ruleFilter, indexCache );
        }
        
        return prepend ( subindices.prepend ( newSubIndex ),
                         oldSubindices,
                         updateTarget );
    }

    
    /**
     * Update the subtree of indices the given iterator
     * <code>pathToModification</code> descends to 
     */
    private ListOfTermTacletAppIndex
	              updateOneSubIndex ( ListOfTermTacletAppIndex oldSubindices,
	                                  PIOPathIterator pathToModification,
	                                  Services        services,
	                                  Constraint      userConstraint,
	                                  TacletIndex     tacletIndex,
	                                  NewRuleListener listener,
                                      ITermTacletAppIndexCache indexCache ) {

        final int child = pathToModification.getChild ();

        ListOfTermTacletAppIndex subindices = oldSubindices.take ( child );                              
        final TermTacletAppIndex toBeUpdated = subindices.head ();
        subindices = subindices.tail ();

        final TermTacletAppIndex newSubIndex =
            toBeUpdated.updateHelp ( pathToModification, services,
                                     userConstraint, tacletIndex, listener,
                                     indexCache );
        
        return prepend ( subindices.prepend ( newSubIndex ), oldSubindices,
                         child );
    }


    /**
     * Prepend the first <code>n</code> elements of <code>toAdd</code> to
     * <code>initialList</code>
     */
    private static ListOfTermTacletAppIndex prepend(ListOfTermTacletAppIndex initialList,
                                                    ListOfTermTacletAppIndex toAdd,
                                                    int n) {
        if ( n <= 0 ) return initialList;
        if ( n == 1 ) return initialList.prepend ( toAdd.head () );
        return prepend ( initialList, toAdd.tail (), n - 1 )
               .prepend ( toAdd.head () );
    }


    /**
     * Updates the TermTacletAppIndex after a change at or below 
     * position <code>pos</code>
     * @param pos Pointer to the term/formula where a change occurred
     * @return the updated index object
     */
    public TermTacletAppIndex update ( PosInOccurrence pos,
                                       Services        services,
                                       Constraint      userConstraint,
                                       TacletIndex     tacletIndex,	
                                       NewRuleListener listener,
                                       TermTacletAppIndexCacheSet indexCaches ) {       
        
        final ITermTacletAppIndexCache indexCache =
            determineIndexCache ( pos, indexCaches, displayConstraint );

        final PIOPathIterator it = pos.iterator ();
        return updateHelp ( it, services, userConstraint, tacletIndex,
                            listener, indexCache );
    }


    /**
     * @return the sub-index for the given position
     */
    private TermTacletAppIndex descend(PosInOccurrence pos) {
        if ( pos.isTopLevel () ) return this;

        final PIOPathIterator it = pos.iterator ();
        TermTacletAppIndex res = this;

        while ( true ) {
            final int child = it.next ();
            if ( child == -1 ) return res;

            res = res.getSubIndex ( child );
        }
    }


    /**
     * @return all taclet apps for the given position
     */
    public ListOfNoPosTacletApp getTacletAppAt(PosInOccurrence pos,
                                               RuleFilter p_filter) {
        TermTacletAppIndex index = descend ( pos );
        return filter ( p_filter, index.localTacletApps );
    }


    /**
     * @return all taclet apps for or below the given position
     */
    public ListOfTacletApp getTacletAppAtAndBelow(PosInOccurrence pos,
                                                  RuleFilter filter) {
        return descend ( pos ).collectTacletApps ( pos, filter );
    }
    
    /**
     * Class that is used to convert <code>NoPosTacletApp</code>s to
     * <code>PosTacletApp</code>s via the method
     * <code>reportTacletApps</code>
     */
    private static class CollectTacletAppListener implements NewRuleListener {
        private ListOfTacletApp res = SLListOfTacletApp.EMPTY_LIST;
        private final RuleFilter filter;
        
        public CollectTacletAppListener ( RuleFilter p_filter ) {
            filter = p_filter;
        }
        
        public ListOfTacletApp getResult () {
            return res;
        }
        
        public void ruleAdded ( RuleApp app, PosInOccurrence pos ) {
            if ( filter.filter( ( app.rule() ) ) ) {
                final TacletApp tacletApp = 
                    TacletAppIndex.createTacletApp( (NoPosTacletApp) app, pos );
                if ( tacletApp != null ) {
                    res = res.prepend ( tacletApp );
                }
            }
        }
    }
    
    /**
     * Collect all taclet apps that are stored by <code>this</code> (and by
     * the sub-indices of <code>this</code>). <code>NoPosTacletApp</code>s are
     * converted to <code>PosTacletApp</code>s using the parameter
     * <code>pos</code>
     * @param pos The position of this index
     * @return a list of all taclet apps
     */
    private ListOfTacletApp collectTacletApps(PosInOccurrence pos,
                                              RuleFilter p_filter) {
        pos = handleDisplayConstraint ( pos, displayConstraint );

        final CollectTacletAppListener listener =
            new CollectTacletAppListener ( p_filter );

        reportTacletApps ( pos, listener );

        return listener.getResult ();
    }
    
    /**
     * Report all <code>NoPosTacletApp</code> s that are stored by
     * <code>this</code> (and by the sub-indices of <code>this</code>).
     * 
     * @param pos
     *            The position of this index
     * @param listener
     *            The listener to which the taclet apps found are supposed to be
     *            reported
     */
    public void reportTacletApps ( PosInOccurrence pos,
                                   NewRuleListener listener ) {
        pos = handleDisplayConstraint ( pos, displayConstraint );
        fireRulesAdded ( listener, localTacletApps, pos );
        
        final IteratorOfTermTacletAppIndex it = subtermIndices.iterator ();
        int subterm = 0;
        while ( it.hasNext () ) {
            it.next ().reportTacletApps ( pos.down ( subterm ),
                                          listener );
            ++subterm;
        }
    }

    /**
     * Report all taclet apps that are affected by a modification of the term
     * under consideration at place <code>pathToModification</code>. These are
     * the taclet above and below the place of modification, and the taclets
     * whose update context has changed.
     */
    private void reportTacletApps ( PIOPathIterator pathToModification,
                                    NewRuleListener listener ) {
        final PosInOccurrence pos = pathToModification.getPosInOccurrence ();
        if ( !pathToModification.hasNext () ) {
            reportTacletApps ( pos, listener );
            return;
        }
        
        fireRulesAdded ( listener, localTacletApps, pos );
        final Term subTerm = pos.subTerm ();
        final int nextSubtermIndex = pathToModification.getChild ();
        
        if ( subTerm.op () instanceof IUpdateOperator ) {
            final int targetPos = ( (IUpdateOperator)subTerm.op () ).targetPos ();
            if ( nextSubtermIndex != targetPos )
                getSubIndex ( targetPos )
                    .reportTacletApps ( pos.down ( targetPos ), listener );
        }
        
        pathToModification.next ();
        getSubIndex ( nextSubtermIndex )
            .reportTacletApps ( pathToModification, listener );
    }
    
    private static void fireRulesAdded(NewRuleListener listener,
                                       ListOfNoPosTacletApp taclets,
                                       PosInOccurrence pos) {
        IteratorOfNoPosTacletApp it = taclets.iterator ();

        while ( it.hasNext () )
            listener.ruleAdded ( it.next (), pos );
    }


    /**
     * @return filtered list
     */
    public static ListOfNoPosTacletApp filter (RuleFilter p_filter,
                                               ListOfNoPosTacletApp taclets) {
        ListOfNoPosTacletApp result = SLListOfNoPosTacletApp.EMPTY_LIST;

        while ( taclets != SLListOfNoPosTacletApp.EMPTY_LIST ) {
            final NoPosTacletApp app = taclets.head ();
            taclets = taclets.tail ();
            if ( p_filter.filter ( app.taclet () ) )
            result = result.prepend ( app );
        }

        return result;
    }
}
