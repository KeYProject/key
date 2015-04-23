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

package de.uka.ilkd.key.proof;

import java.util.Iterator;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMap;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.rulefilter.AndRuleFilter;
import de.uka.ilkd.key.proof.rulefilter.RuleFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * Class whose objects represent an index of taclet apps for one particular
 * position within a formula, and that also contain references to the indices of
 * direct subformulas
 */
public class TermTacletAppIndex {
    /** the term for which NoPosTacletApps are kept in this index node */
    private final Term term;
    /** NoPosTacletApps for this term */
    private final ImmutableList<NoPosTacletApp> localTacletApps;
    /** indices for subterms */
    private final ImmutableList<TermTacletAppIndex> subtermIndices;
    /** */
    private final RuleFilter ruleFilter;

    /**
     * Create a TermTacletAppIndex
     */
    private TermTacletAppIndex( Term term,
                                ImmutableList<NoPosTacletApp> localTacletApps,
                                ImmutableList<TermTacletAppIndex> subtermIndices,
                                RuleFilter ruleFilter ) {
        this.term              = term;
        this.subtermIndices    = subtermIndices;
        this.localTacletApps   = localTacletApps;
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
    private static ImmutableList<NoPosTacletApp> getRewriteTaclet(PosInOccurrence pos,
                                                         RuleFilter      filter,
                                                         Services        services,
                                                         TacletIndex     tacletIndex) {

        return tacletIndex.getRewriteTaclet(pos, filter, services);
    }
  
    /** 
     * collects all FindTaclets with instantiations for the given
     * heuristics and position
     * @param pos the PosInOccurrence to focus
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ImmutableList<NoPosTacletApp> getFindTaclet(PosInOccurrence pos,
                                                      RuleFilter      filter,
                                                      Services        services,
                                                      TacletIndex     tacletIndex) { 
        ImmutableList<NoPosTacletApp> tacletInsts = ImmutableSLList.<NoPosTacletApp>nil();
        if ( pos.isTopLevel () ) {
            if ( pos.isInAntec () ) {
                tacletInsts =
                    tacletInsts.prepend ( antecTaclet ( pos, filter, services,
                                                        tacletIndex ) );
            } else {
                tacletInsts =
                    tacletInsts.prepend ( succTaclet ( pos, filter, services,
                                                       tacletIndex ) );
            }
        } else {
            tacletInsts =
                tacletInsts.prepend ( getRewriteTaclet ( pos, filter, services,
                                                         tacletIndex ) );
        }
        return tacletInsts;
    }


    /** 
     * collects all AntecedentTaclet instantiations for the given
     * heuristics and SequentFormula
     * @param pos the PosInOccurrence of the SequentFormula 
     *  the taclets have to be connected to 
     * (pos must point to the top level formula, i.e. <tt>pos.isTopLevel()</tt> must be true)     
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ImmutableList<NoPosTacletApp> antecTaclet(PosInOccurrence pos,
                                                    RuleFilter filter,
                                                    Services services,
                                                    TacletIndex tacletIndex) {
        return tacletIndex.getAntecedentTaclet ( pos, filter, services );
    }
    
    /** 
     * collects all SuccedentTaclet instantiations for the given
     * heuristics and SequentFormula
     * @param pos the PosInOccurrence of the SequentFormula 
     *  the taclets have to be connected to 
     * (pos must point to the top level formula, 
     * i.e. <tt>pos.isTopLevel()</tt> must be true)     
     * @param services the Services object encapsulating information
     * about the java datastructures like (static)types etc.
     * @return list of all possible instantiations
     */
    private static ImmutableList<NoPosTacletApp> succTaclet(PosInOccurrence pos,
                                                   RuleFilter filter,
                                                   Services services,
                                                   TacletIndex tacletIndex) {
        return tacletIndex.getSuccedentTaclet ( pos, filter, services );
    }

    /**
     * Descend and create indices for each of the direct subterms of
     * the given term
     * @param pos pointer to the term/formula for whose subterms
     * indices are to be created
     * @return list of the index objects
     */
    private static ImmutableList<TermTacletAppIndex>
                   createSubIndices (PosInOccurrence pos,
                                     Services        services,
                                     TacletIndex     tacletIndex,
                                     NewRuleListener listener,
                                     RuleFilter      filter,
                                     ITermTacletAppIndexCache indexCache) {
        ImmutableList<TermTacletAppIndex> result = ImmutableSLList.<TermTacletAppIndex>nil();
        final Term localTerm = pos.subTerm ();

        int i = localTerm.arity();

        while ( i-- != 0 )
            result = result.prepend ( createHelp ( pos.down(i),
                                                   services,
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
                                            TacletIndex     tacletIndex,
                                            NewRuleListener listener,
                                            RuleFilter      filter,
                                            TermTacletAppIndexCacheSet indexCaches) {
        assert pos.isTopLevel () : "Someone tried to create a term index for a real subterm";

        final ITermTacletAppIndexCache indexCache =
            determineIndexCache ( pos, indexCaches );
        
        return createHelp ( pos, services, tacletIndex,
                            listener, filter, indexCache );
    }

    private static ITermTacletAppIndexCache
                   determineIndexCache(PosInOccurrence pos,
                                       TermTacletAppIndexCacheSet indexCaches) {       
        if ( pos.isInAntec () )
            return indexCaches.getAntecCache ();
        else
            return indexCaches.getSuccCache ();
    }


    private static TermTacletAppIndex createHelp(PosInOccurrence pos,
                                                 Services        services,
                                                 TacletIndex     tacletIndex,
                                                 NewRuleListener listener,
                                                 RuleFilter      filter,
                                                 ITermTacletAppIndexCache indexCache) {
        final Term localTerm = pos.subTerm ();

        final TermTacletAppIndex cached = indexCache.getIndexForTerm ( localTerm );
        if ( cached != null ) {
            cached.reportTacletApps ( pos, listener );
            return cached;
        }

        final ImmutableList<NoPosTacletApp> localApps = getFindTaclet ( pos, filter,
                                                                        services,
                                                                        tacletIndex );

        final ImmutableList<TermTacletAppIndex> subIndices =
            createSubIndices ( pos, services, tacletIndex,
                               listener, filter, indexCache );

        fireRulesAdded ( listener, localApps, pos );

        final TermTacletAppIndex res = new TermTacletAppIndex ( localTerm,
                                                                localApps,
                                                                subIndices,
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
                                         TacletIndex     tacletIndex,
                                         NewRuleListener listener) {
        RuleFilter effectiveFilter = new AndRuleFilter ( filter, ruleFilter );

        return addTacletsHelp ( effectiveFilter, pos, services, tacletIndex,
                                listener );
    }

    private TermTacletAppIndex addTacletsHelp(RuleFilter      filter,
                                              PosInOccurrence pos,
                                              Services        services,
                                              TacletIndex     tacletIndex,
                                              NewRuleListener listener) {

        final ImmutableList<TermTacletAppIndex> newSubIndices =
            addTacletsSubIndices ( filter, pos, services, tacletIndex,
                                   listener );
	
        final ImmutableList<NoPosTacletApp> additionalApps =
            getFindTaclet ( pos, filter, services, tacletIndex );

        fireRulesAdded ( listener, additionalApps, pos );
			    
        return new TermTacletAppIndex ( term,
                                        localTacletApps.prepend ( additionalApps ),
                                        newSubIndices,
                                        ruleFilter );
    }


    private ImmutableList<TermTacletAppIndex> addTacletsSubIndices( RuleFilter      filter,
                                                           PosInOccurrence pos,
                                                           Services        services,
                                                           TacletIndex     tacletIndex,
                                                           NewRuleListener listener ) {
        ImmutableList<TermTacletAppIndex> result = ImmutableSLList.<TermTacletAppIndex>nil();
        final Iterator<TermTacletAppIndex> subIt = subtermIndices.iterator();
        
        int i = 0;
        while ( subIt.hasNext () ) {
            final TermTacletAppIndex oldSubIndex = subIt.next ();
            final TermTacletAppIndex newSubIndex =
                oldSubIndex.addTacletsHelp ( filter, pos.down ( i ), services,
                                             tacletIndex, listener );
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
                                          TacletIndex tacletIndex,
                                          NewRuleListener listener,
                                          ITermTacletAppIndexCache indexCache) {

        pathToModification.next ();

        // Below the position of modification everything has to be rebuilt
        final boolean completeRebuild = !pathToModification.hasNext ();
        final PosInOccurrence pos = pathToModification.getPosInOccurrence ();

        if ( completeRebuild )
            return updateCompleteRebuild ( pos, services, tacletIndex,
                                           listener, indexCache );

        final Term newTerm = pathToModification.getSubTerm ();

        final TermTacletAppIndex cached = indexCache.getIndexForTerm ( newTerm );
        if ( cached != null ) {
            cached.reportTacletApps ( pathToModification, listener );
            return cached;
        }

        final ImmutableList<TermTacletAppIndex> newSubIndices =
            updateSubIndexes ( pathToModification, services, tacletIndex,
                               listener, indexCache );
            
        final TermTacletAppIndex res =
            updateLocalApps ( pos, newTerm, services, tacletIndex,
                              listener, newSubIndices );
        
        indexCache.putIndexForTerm ( newTerm, res );
        return res;
    }


    private TermTacletAppIndex updateCompleteRebuild(PosInOccurrence pos,
                                                     Services services,
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
            return updateLocalApps ( pos, newTerm, services, tacletIndex,
                                     listener, subtermIndices );
        }
        
        return createHelp ( pos, services, tacletIndex, listener,
                            ruleFilter, indexCache );
    }


    private TermTacletAppIndex updateLocalApps(PosInOccurrence pos,
                                               Term newSubterm,
                                               Services services,
                                               TacletIndex tacletIndex,
                                               NewRuleListener listener,
                                               ImmutableList<TermTacletAppIndex> newSubIndices) {
        final ImmutableList<NoPosTacletApp> localApps = getFindTaclet ( pos, ruleFilter,
                                                               services,
                                                               tacletIndex );

        fireRulesAdded ( listener, localApps, pos );

        return new TermTacletAppIndex ( newSubterm, localApps, newSubIndices,
                                        ruleFilter );
    }


    private ImmutableList<TermTacletAppIndex>
               updateSubIndexes(PIOPathIterator pathToModification,
                                Services services,
                                TacletIndex tacletIndex,
                                NewRuleListener listener,
                                ITermTacletAppIndexCache indexCache) {
        ImmutableList<TermTacletAppIndex> newSubIndices = subtermIndices;
        
        final Term newTerm = pathToModification.getSubTerm ();
        final int child = pathToModification.getChild ();
        
        if ( newTerm.op () instanceof UpdateApplication ) {
            final int targetPos = UpdateApplication.targetPos ();
            if ( child != targetPos ) {
                newSubIndices =
                    updateIUpdateTarget ( newSubIndices,
                                          targetPos,
                                          pathToModification.getPosInOccurrence ()
                                                            .down ( targetPos ),
                                          services,
                                          tacletIndex,
                                          listener,
                                          indexCache.descend ( newTerm, targetPos ) );
            }
        }
        
        return updateOneSubIndex ( newSubIndices, pathToModification, services,
                                   tacletIndex, listener, indexCache.descend ( newTerm, child ) );
    }

    
    /**
     * Update the target formula/term of an update (which has position
     * <code>subtermPos</code> in the complete formula). This is necessary
     * whenever a part of the update has changed, because this also changes the
     * update context of taclet apps in the target.
     */
    private ImmutableList<TermTacletAppIndex>
                 updateIUpdateTarget ( ImmutableList<TermTacletAppIndex> oldSubindices,
                                       int             updateTarget,
                                       PosInOccurrence targetPos,
                                       Services        services,
                                       TacletIndex     tacletIndex,
                                       NewRuleListener listener,
                                       ITermTacletAppIndexCache indexCache ) {

        ImmutableList<TermTacletAppIndex> subindices = oldSubindices.take ( updateTarget );                              
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
                                                        services, tacletIndex,
                                                        listener, toBeRemoved.subtermIndices );
        } else {
            // the target is updated completely otherwise
            newSubIndex = createHelp ( targetPos, services, tacletIndex,
                                       listener,
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
    private ImmutableList<TermTacletAppIndex>
	              updateOneSubIndex ( ImmutableList<TermTacletAppIndex> oldSubindices,
	                                  PIOPathIterator pathToModification,
	                                  Services        services,
	                                  TacletIndex     tacletIndex,
	                                  NewRuleListener listener,
	                                  ITermTacletAppIndexCache indexCache ) {

        final int child = pathToModification.getChild ();

        ImmutableList<TermTacletAppIndex> subindices = oldSubindices.take ( child );                              
        final TermTacletAppIndex toBeUpdated = subindices.head ();
        subindices = subindices.tail ();

        final TermTacletAppIndex newSubIndex =
            toBeUpdated.updateHelp ( pathToModification, services,
                                     tacletIndex, listener, indexCache );
        
        return prepend ( subindices.prepend ( newSubIndex ), oldSubindices,
                         child );
    }


    /**
     * Prepend the first <code>n</code> elements of <code>toAdd</code> to
     * <code>initialList</code>
     */
    private static ImmutableList<TermTacletAppIndex> prepend(ImmutableList<TermTacletAppIndex> initialList,
                                                    ImmutableList<TermTacletAppIndex> toAdd,
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
    TermTacletAppIndex update ( PosInOccurrence pos,
                                Services        services,
                                TacletIndex     tacletIndex,
                                NewRuleListener listener,	
                                TermTacletAppIndexCacheSet indexCaches ) {       
        
        final ITermTacletAppIndexCache indexCache =
            determineIndexCache ( pos, indexCaches );

        final PIOPathIterator it = pos.iterator ();
        return updateHelp ( it, services, tacletIndex, listener,
                            indexCache );
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
    public ImmutableList<NoPosTacletApp> getTacletAppAt(PosInOccurrence pos,
                                               RuleFilter p_filter) {
        TermTacletAppIndex index = descend ( pos );
        return filter ( p_filter, index.localTacletApps );
    }


    /**
     * @return all taclet apps for or below the given position
     */
    public ImmutableList<TacletApp> getTacletAppAtAndBelow(PosInOccurrence pos,
                                                  RuleFilter filter,
                                                  Services services) {
        return descend ( pos ).collectTacletApps ( pos, filter, services );
    }
    
    private ImmutableList<TacletApp> convert(ImmutableList<? extends RuleApp> rules, PosInOccurrence pos, 
            RuleFilter filter, ImmutableList<TacletApp> convertedApps, Services services) {

        for (final RuleApp app : rules) {
            if ( filter.filter( ( app.rule() ) ) ) {
                final TacletApp tacletApp = 
                        TacletAppIndex.createTacletApp( (NoPosTacletApp) app, pos, services );
                if ( tacletApp != null ) {
                    convertedApps = convertedApps.prepend ( tacletApp );
                }
            }
        }

        return convertedApps;
    }

    
    /**
     * Collect all taclet apps that are stored by <code>this</code> (and by
     * the sub-indices of <code>this</code>). <code>NoPosTacletApp</code>s are
     * converted to <code>PosTacletApp</code>s using the parameter
     * <code>pos</code>
     * @param pos The position of this index
     * @return a list of all taclet apps
     */
    private ImmutableList<TacletApp> collectTacletApps(PosInOccurrence pos,
                                              RuleFilter p_filter,
                                              Services services) {
        
        ImmutableList<TacletApp> result = ImmutableSLList.<TacletApp>nil();
        
        final ImmutableMap<PosInOccurrence,ImmutableList<NoPosTacletApp>> allTacletsHereAndBelow = 
                collectAllTacletAppsHereAndBelow( pos,  DefaultImmutableMap.<PosInOccurrence, ImmutableList<NoPosTacletApp>>nilMap() );
        
        for (final ImmutableMapEntry<PosInOccurrence,ImmutableList<NoPosTacletApp>> pair : allTacletsHereAndBelow) {
            result = convert(pair.value(), pair.key(), p_filter, result, services);
        }

        return result;
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
    void reportTacletApps ( PosInOccurrence pos,
                            NewRuleListener listener ) {
                
        final ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>> result = 
                DefaultImmutableMap.<PosInOccurrence, ImmutableList<NoPosTacletApp>>nilMap();
        final ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>> allTacletsHereAndBelow = 
                collectAllTacletAppsHereAndBelow( pos, result );
        for (final ImmutableMapEntry<PosInOccurrence,ImmutableList<NoPosTacletApp>> pair : allTacletsHereAndBelow) {
            fireRulesAdded ( listener, pair.value(), pair.key() );
        }
    }
        
    /**
     * Collect all <code>NoPosTacletApp</code> s that are stored by
     * <code>this</code> (and by the sub-indices of <code>this</code>).
     * 
     * @param pos
     *            The position of this index
     * @param collectedApps
     *            the {@link ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>>} to which to 
     *            add the found taclet applications; it must not contain 
     *            {@code pos} or any position below pos as key 
     * @return the resulting list of taclet applications from this and all subterm taclet indices
     */
    private ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>> collectAllTacletAppsHereAndBelow 
        ( PosInOccurrence pos,
                ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>> collectedApps ) {
    
        // assert collectedApps.get(pos) == null;
        collectedApps = collectedApps.put(pos, localTacletApps);

        int subterm = 0;
        for (final TermTacletAppIndex appIndex : subtermIndices) {
            collectedApps = appIndex.collectAllTacletAppsHereAndBelow ( pos.down ( subterm ), collectedApps );
            ++subterm;
        }
        
        return collectedApps;
    }

    /**
     * Report all taclet apps that are affected by a modification of the term
     * under consideration at place <code>pathToModification</code>. These are
     * the taclet above and below the place of modification, and the taclets
     * whose update context has changed.
     */
    private void reportTacletApps ( PIOPathIterator pathToModification,
                                    NewRuleListener listener ) {
        final ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>> allTacletsHereAndBelow = 
                collectAllTacletAppsAffectedByModification ( pathToModification, 
                DefaultImmutableMap.<PosInOccurrence, ImmutableList<NoPosTacletApp>>nilMap() ); 
        
        for (final ImmutableMapEntry<PosInOccurrence,ImmutableList<NoPosTacletApp>> pair  : allTacletsHereAndBelow ) {
            fireRulesAdded ( listener, pair.value(), pair.key() );
        }
    }
    
    /**
     * Collects all taclet apps that are affected by a modification of the term
     * under consideration at place <code>pathToModification</code>. These are
     * the taclet above and below the place of modification, and the taclets
     * whose update context has changed.
     * <strong>The map of already collected apps must not contain any entry for a position on or below the path to modification.</strong> 
     * @return all affected taclet apps grouped by the corresponding {@link PosInOccurrence}
     */
    private  ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>> collectAllTacletAppsAffectedByModification 
            ( PIOPathIterator pathToModification, ImmutableMap<PosInOccurrence, ImmutableList<NoPosTacletApp>> collectedApps ) {
        
        TermTacletAppIndex index = this;        
        PosInOccurrence pos = pathToModification.getPosInOccurrence ();
        
        while ( pathToModification.hasNext () ) {
            // assert collectedApps.get(pos) == null;
            collectedApps = collectedApps.put(pos, index.localTacletApps);

            final Term subTerm = pos.subTerm ();
            final int nextSubtermIndex = pathToModification.getChild ();

            if ( subTerm.op () instanceof UpdateApplication ) {
                final int targetPos = UpdateApplication.targetPos ();
                if ( nextSubtermIndex != targetPos ) {
                    // the path to modification leads to a place inside an update
                    // i.e., we have to collect all taclets matching behind the update
                    // as their update context has changed
                    collectedApps = index.getSubIndex ( targetPos )
                    .collectAllTacletAppsHereAndBelow ( pos.down ( targetPos ), collectedApps );
                }
            }

            index = index.getSubIndex ( nextSubtermIndex );
            pathToModification.next ();
            pos = pathToModification.getPosInOccurrence ();
        }
        
        collectedApps = index.collectAllTacletAppsHereAndBelow ( pos, collectedApps );
        
        return collectedApps;
    }
    
    private static void fireRulesAdded(NewRuleListener listener,
                                       ImmutableList<NoPosTacletApp> taclets,
                                       PosInOccurrence pos) {
        listener.rulesAdded(taclets, pos);
    }


    /**
     * @return filtered list
     */
    public static ImmutableList<NoPosTacletApp> filter (RuleFilter p_filter,
                                               ImmutableList<NoPosTacletApp> taclets) {
        ImmutableList<NoPosTacletApp> result = ImmutableSLList.<NoPosTacletApp>nil();

        for (final NoPosTacletApp app :  taclets) {
            if ( p_filter.filter ( app.taclet () ) ) {
                result = result.prepend ( app );
            }
        }

        return result;
    }
}