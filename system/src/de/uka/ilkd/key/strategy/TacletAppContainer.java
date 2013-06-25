// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.strategy;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.util.Debug;

/**
 * Instances of this class are immutable
 */
public abstract class TacletAppContainer extends RuleAppContainer {

    private final long age;

    protected TacletAppContainer ( RuleApp     p_app,
				   RuleAppCost p_cost,
                                   long        p_age ) {
	super ( p_app, p_cost );
	age = p_age;
    }


    protected NoPosTacletApp getTacletApp () {
	return (NoPosTacletApp)getRuleApp();
    }

    public long getAge () {
        return age;
    }

    private ImmutableList<TacletApp> incMatchIfFormulas (Goal p_goal) {
        final IfInstantiator instantiator = new IfInstantiator ( p_goal );
        instantiator.findIfFormulaInstantiations ();
        return instantiator.getResults ();
    }

    protected static TacletAppContainer createContainer(RuleApp p_app,
                                                        PosInOccurrence p_pio,
                                                        Goal p_goal,
                                                        Strategy p_strategy,
                                                        boolean p_initial) {
        return createContainer ( p_app, p_pio, p_goal,
                                 p_strategy.computeCost ( p_app, p_pio, p_goal ),
                                 p_initial );
    }

    private static TacletAppContainer createContainer(RuleApp p_app,
                                                      PosInOccurrence p_pio,
                                                      Goal p_goal,
                                                      RuleAppCost p_cost,
                                                      boolean p_initial) {
        // This relies on the fact that the method <code>Goal.getTime()</code>
        // never returns a value less than zero
        final long        localage  = p_initial ? -1 : p_goal.getTime();
        if ( p_pio == null )
            return new NoFindTacletAppContainer ( p_app, p_cost, localage );
        else
            return new FindTacletAppContainer ( p_app, p_pio, p_cost, p_goal, localage );
    }


    /**
     * Create a list of new RuleAppContainers that are to be
     * considered for application.
     */
    public final ImmutableList<RuleAppContainer> createFurtherApps (Goal p_goal,
                                                     Strategy p_strategy) {
        if ( !isStillApplicable ( p_goal )
             ||
             getTacletApp ().ifInstsComplete ()
             && !ifFormulasStillValid ( p_goal ))
            return ImmutableSLList.<RuleAppContainer>nil();

        final TacletAppContainer newCont = createContainer ( p_goal, p_strategy );
        if ( newCont.getCost () instanceof TopRuleAppCost )
            return ImmutableSLList.<RuleAppContainer>nil();

        ImmutableList<RuleAppContainer> res =
            ImmutableSLList.<RuleAppContainer>nil().prepend ( newCont );

        if ( getTacletApp ().ifInstsComplete () ) {
            res = addInstances ( getTacletApp (), res, p_goal, p_strategy );
        } else {
            for (TacletApp tacletApp : incMatchIfFormulas(p_goal)) {
                final TacletApp app = tacletApp;
                res = addContainer(app, res, p_goal, p_strategy);
                res = addInstances(app, res, p_goal, p_strategy);
            }
        }

        return res;
    }


    /**
     * Add all instances of the given taclet app (that are possibly produced
     * using method <code>instantiateApp</code> of the strategy) to
     * <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addInstances( TacletApp app,
                                                 ImmutableList<RuleAppContainer> targetList,
                                                 Goal p_goal,
                                                 Strategy p_strategy) {
        if ( app.uninstantiatedVars ().size () == 0 ) return targetList;
        return instantiateApp ( app, targetList, p_goal, p_strategy );
    }

    /**
     * Use the method <code>instantiateApp</code> of the strategy for choosing
     * the values of schema variables that have not been instantiated so far
     */
    private ImmutableList<RuleAppContainer> instantiateApp(TacletApp app,
                                                  ImmutableList<RuleAppContainer> targetList,
                                                  final Goal p_goal,
                                                  Strategy p_strategy) {
        // just for being able to modify the result-list in an
        // anonymous class
        @SuppressWarnings("unchecked")
        final ImmutableList<RuleAppContainer>[] resA =  new ImmutableList[] { targetList };

        final RuleAppCostCollector collector =
            new RuleAppCostCollector () {
                public void collect(RuleApp newApp, RuleAppCost cost) {
                    if (cost instanceof TopRuleAppCost) return;
                    resA[0] = addContainer ( (TacletApp)newApp,
                                             resA[0],
                                             p_goal,
                                             cost );
                }
            };
        p_strategy.instantiateApp ( app,
                                    getPosInOccurrence ( p_goal ),
                                    p_goal,
                                    collector );

        return resA[0];
    }

    /**
     * Create a container object for the given taclet app, provided that the app
     * is <code>sufficientlyComplete</code>, and add the container to
     * <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addContainer(TacletApp app,
                                                ImmutableList<RuleAppContainer> targetList,
                                                Goal p_goal,
                                                Strategy p_strategy) {
        return targetList.prepend ( TacletAppContainer
                                    .createContainer ( app,
                                                       getPosInOccurrence ( p_goal ),
                                                       p_goal,
                                                       p_strategy,
                                                       false ) );
    }

    /**
     * Create a container object for the given taclet app, provided that the app
     * is <code>sufficientlyComplete</code>, and add the container to
     * <code>targetList</code>
     */
    private ImmutableList<RuleAppContainer> addContainer(TacletApp app,
                                                ImmutableList<RuleAppContainer> targetList,
                                                Goal p_goal,
                                                RuleAppCost cost) {
        if ( !sufficientlyCompleteApp ( app, p_goal.proof().getServices() ) ) return targetList;
        return targetList.prepend ( TacletAppContainer
                                    .createContainer ( app,
                                                       getPosInOccurrence ( p_goal ),
                                                       p_goal,
                                                       cost,
                                                       false ) );
    }

    private boolean sufficientlyCompleteApp(TacletApp app, Services services) {
        final ImmutableSet<SchemaVariable> needed = app.uninstantiatedVars ();
        if ( needed.size () == 0 ) return true;
        for (SchemaVariable aNeeded : needed) {
            final SchemaVariable sv = aNeeded;
            if ( sv instanceof SkolemTermSV ) continue;
            return false;
        }
        return true;
    }

    private TacletAppContainer createContainer (Goal p_goal, Strategy p_strategy) {
        return createContainer ( getTacletApp (),
                                 getPosInOccurrence ( p_goal ),
                                 p_goal,
                                 p_strategy,
                                 false );
    }


    /**
     * Create containers for NoFindTaclets.
     */
    static ImmutableList<RuleAppContainer> createAppContainers
        ( NoPosTacletApp p_app, Goal p_goal, Strategy  p_strategy ) {
	return createAppContainers ( p_app, null, p_goal, p_strategy );
    }

    /**
     * Create containers for FindTaclets or NoFindTaclets.
     * @param p_app if <code>p_pio</code> is null, <code>p_app</code> has to be
     * a <code>TacletApp</code> for a <code>NoFindTaclet</code>,
     * otherwise for a <code>FindTaclet</code>.
     * @return list of containers for currently applicable TacletApps, the cost
     * may be an instance of <code>TopRuleAppCost</code>.
     */
    static ImmutableList<RuleAppContainer> createAppContainers
        ( NoPosTacletApp  p_app,
          PosInOccurrence p_pio,
          Goal            p_goal,
          Strategy        p_strategy ) {
        if ( !( p_pio == null
                ? p_app.taclet () instanceof NoFindTaclet
                : p_app.taclet () instanceof FindTaclet ) )
            // faster than <code>assertTrue</code>
	    Debug.fail ( "Wrong type of taclet " + p_app.taclet () );

        // Create an initial container for the given taclet; the if-formulas of
        // the taclet are only matched lazy (by <code>createFurtherApps()</code>
        return ImmutableSLList.<RuleAppContainer>nil()
                    .prepend ( createContainer ( p_app,
                                                 p_pio,
                                                 p_goal,
                                                 p_strategy,
                                                 true ) );
    }

    /**
     * @return true iff instantiation of the if-formulas of the stored taclet
     * app exist and are valid are still valid, i.e. the referenced formulas
     * still exist
     */
    protected boolean ifFormulasStillValid ( Goal p_goal ) {
    	if ( getTacletApp().taclet().ifSequent().isEmpty() )
    	    return true;
    	if ( !getTacletApp().ifInstsComplete() )
    	    return false;

    	final Iterator<IfFormulaInstantiation> it =
    	    getTacletApp().ifFormulaInstantiations().iterator();
	final Sequent seq = p_goal.sequent();

	while ( it.hasNext () ) {
	    final IfFormulaInstantiation ifInst2 = it.next ();
            if ( !( ifInst2 instanceof IfFormulaInstSeq ) )
                // faster than assertTrue
	        Debug.fail ( "Don't know what to do with the " +
                             "if-instantiation " + ifInst2 );
	    final IfFormulaInstSeq ifInst = (IfFormulaInstSeq)ifInst2;
	    if ( !( ifInst.inAntec() ? seq.antecedent() : seq.succedent() )
	          .contains ( ifInst.getConstrainedFormula() ) )
		return false;
	}

	return true;
    }

    /**
     * @return true iff the stored rule app is applicable for the given sequent,
     * i.e. if the find-position does still exist (if-formulas are not
     * considered)
     */
    protected abstract boolean isStillApplicable ( Goal p_goal );


    protected PosInOccurrence getPosInOccurrence ( Goal p_goal ) {
    	return null;
    }


    /**
     * Create a <code>RuleApp</code> that is suitable to be applied
     * or <code>null</code>.
     */
    public RuleApp completeRuleApp(Goal p_goal, Strategy strategy) {
        if ( !isStillApplicable ( p_goal ) )
            return null;

        if ( !ifFormulasStillValid ( p_goal ) )
            return null;

        TacletApp app = getTacletApp ();

        final PosInOccurrence pio = getPosInOccurrence ( p_goal );
        if ( !strategy.isApprovedApp(app, pio, p_goal) ) return null;

        if ( pio != null ) {
            app = app.setPosInOccurrence ( pio, p_goal.proof().getServices() );
            if ( app == null ) return null;
        }

        if ( !app.complete() )
            app = app.tryToInstantiate ( p_goal.proof().getServices() );

        return app;
    }

    /**
     * This class implements custom instantiation of if-formulas.
     */
    private class IfInstantiator {
        private final Goal      goal;

        private ImmutableList<IfFormulaInstantiation> allAntecFormulas;
        private ImmutableList<IfFormulaInstantiation> allSuccFormulas;

        private ImmutableList<TacletApp> results = ImmutableSLList.<TacletApp>nil();

        IfInstantiator ( final Goal goal ) {
            this.goal = goal;
        }

        private void addResult (TacletApp app) {
            if ( app == null ) return;
            results = results.prepend ( app );
            /*
            final RuleAppContainer cont =
                TacletAppContainer.createContainer ( app,
                                                     getPosInOccurrence ( goal ),
                                                     goal,
                                                     strategy,
                                                     false );
            results = results.prepend ( cont );
            */
        }

        /**
         * Find all possible instantiations of the if sequent formulas
         * within the sequent "p_seq".
         */
        public void findIfFormulaInstantiations () {
            final Sequent p_seq = goal.sequent();

            Debug.assertTrue ( getTacletApp().ifFormulaInstantiations() == null,
                   "The if formulas have already been instantiated" );

            if ( getTaclet ().ifSequent ().isEmpty() )
                addResult ( getTacletApp () );
            else {
                allAntecFormulas = IfFormulaInstSeq.createList(
		    p_seq, true);
                allSuccFormulas  = IfFormulaInstSeq.createList(
		    p_seq, false);
                findIfFormulaInstantiationsHelp
                    ( createSemisequentList ( getTaclet ().ifSequent ()  // Matching starting
                                  .succedent () ),                       // with the last formula
                      createSemisequentList ( getTaclet ().ifSequent ()
                                  .antecedent () ),
                      ImmutableSLList.<IfFormulaInstantiation>nil(),
                      getTacletApp ().matchConditions (),
                      false );
            }
        }


        private Taclet getTaclet () {
            return getTacletApp ().taclet ();
        }


        /**
         * @param p_all
         *            if true then return all formulas of the particular
         *            semisequent, otherwise only the formulas returned by
         *            <code>selectNewFormulas</code>
         * @return a list of potential if-formula instantiations (analogously to
         *         <code>IfFormulaInstSeq.createList</code>)
         */
        private ImmutableList<IfFormulaInstantiation> getSequentFormulas ( boolean p_antec,
                                                                  boolean p_all ) {
            if ( p_all ) return getAllSequentFormulas ( p_antec );

            final ImmutableList<IfFormulaInstantiation> cache =
                getNewSequentFormulasFromCache(p_antec);
            if ( cache != null ) return cache;

            final ImmutableList<IfFormulaInstantiation> newFormulas =
                selectNewFormulas ( p_antec );

            addNewSequentFormulasToCache(newFormulas, p_antec);

            return newFormulas;
        }

        /**
         * @return a list of potential if-formula instantiations (analogously to
         *         <code>IfFormulaInstSeq.createList</code>), but consisting
         *         only of those formulas of the current goal for which the
         *         method <code>isNewFormula</code> returns <code>true</code>
         */
        private ImmutableList<IfFormulaInstantiation> selectNewFormulas (boolean p_antec) {
            final Iterator<IfFormulaInstantiation> it =
                getAllSequentFormulas ( p_antec ).iterator ();
            ImmutableList<IfFormulaInstantiation> res =
                ImmutableSLList.<IfFormulaInstantiation>nil();

            while ( it.hasNext () ) {
                final IfFormulaInstantiation ifInstantiation = it.next ();
                if ( isNewFormulaDirect ( ifInstantiation ) )
                    res = res.prepend ( ifInstantiation );
            }

            return res;
        }

        /**
         * @return true iff the formula described by the argument has been
         *         modified (or introduced) since the latest point of time when
         *         the if-formulas of the enclosing taclet app (container) have
         *         been matched
         */
        private boolean isNewFormula (IfFormulaInstantiation p_ifInstantiation) {
            final boolean antec = ( (IfFormulaInstSeq)p_ifInstantiation ).inAntec ();

            final ImmutableList<IfFormulaInstantiation> cache =
                            getNewSequentFormulasFromCache ( antec );

            if ( cache != null ) return cache.contains ( p_ifInstantiation );

            return isNewFormulaDirect ( p_ifInstantiation );
        }

        /**
         * @return true iff the formula described by the argument has been
         *         modified (or introduced) since the latest point of time when
         *         the if-formulas of the enclosing taclet app (container) have
         *         been matched (this method does not use the cache)
         */
        private boolean isNewFormulaDirect (IfFormulaInstantiation p_ifInstantiation) {
            final boolean antec = ( (IfFormulaInstSeq)p_ifInstantiation ).inAntec ();

            final SequentFormula cfma = p_ifInstantiation.getConstrainedFormula ();
            final PosInOccurrence pio = new PosInOccurrence ( cfma,
                                                              PosInTerm.TOP_LEVEL,
                                                              antec );

            final FormulaTagManager tagManager = goal.getFormulaTagManager ();

            final FormulaTag tag = tagManager.getTagForPos ( pio );
            final long formulaAge = tagManager.getAgeForTag ( tag );

            // The strict relation can be used, because when applying a rule the
            // age of a goal is increased before the actual modification of the
            // goal take place
            return getAge () < formulaAge;
        }

        private ImmutableList<IfFormulaInstantiation>
                    getNewSequentFormulasFromCache (boolean p_antec) {
            synchronized ( ifInstCache ) {
                if ( ifInstCache.cacheKey != goal.node () ) return null;

                // the cache contains formula lists for the right semisequent
                return getCacheMap ( p_antec ).get ( getAgeObject () );
            }
        }

        private void addNewSequentFormulasToCache (ImmutableList<IfFormulaInstantiation> p_list,
                                                   boolean p_antec) {
            synchronized ( ifInstCache ) {
                if ( ifInstCache.cacheKey != goal.node () ) {
                    ifInstCache.reset(goal.node());
                }

                getCacheMap ( p_antec ).put ( getAgeObject (), p_list );
            }
        }


        private HashMap<Long, ImmutableList<IfFormulaInstantiation>> getCacheMap (boolean p_antec) {
            return p_antec ? ifInstCache.antecCache : ifInstCache.succCache;
        }

        private Long getAgeObject () {
            return Long.valueOf( getAge() );
        }


        private ImmutableList<IfFormulaInstantiation> getAllSequentFormulas ( boolean p_antec ) {
            return p_antec ? allAntecFormulas : allSuccFormulas;
        }


        /**
         * Recursive function for matching the remaining tail of an if sequent
         *
         * @param p_ifSeqTail
         *            tail of the current semisequent as list
         * @param p_ifSeqTail2nd
         *            the following semisequent (i.e. antecedent) or null
         * @param p_matchCond
         *            match conditions until now, i.e. after matching the first
         *            formulas of the if sequent
         * @param p_alreadyMatchedNewFor
         *            at least one new formula has already been matched, i.e. a
         *            formula that has been modified recently
         */
        private void findIfFormulaInstantiationsHelp
            ( ImmutableList<SequentFormula>      p_ifSeqTail,
              ImmutableList<SequentFormula>      p_ifSeqTail2nd,
              ImmutableList<IfFormulaInstantiation>  p_alreadyMatched,
              MatchConditions               p_matchCond,
              boolean                       p_alreadyMatchedNewFor ) {

            while ( p_ifSeqTail.isEmpty () ) {
                if ( p_ifSeqTail2nd == null ) {
                    // All formulas have been matched, collect the results
                    addResult ( setAllInstantiations ( p_matchCond,
                                                       p_alreadyMatched ) );
                    return;
                } else {
                    // Change from succedent to antecedent
                    p_ifSeqTail    = p_ifSeqTail2nd;
                    p_ifSeqTail2nd = null;
                }
            }

            // Match the current formula
            final boolean antec = p_ifSeqTail2nd == null;
            final boolean lastIfFormula =
                p_ifSeqTail.size () == 1
                && ( p_ifSeqTail2nd == null || p_ifSeqTail2nd.isEmpty () );
            final ImmutableList<IfFormulaInstantiation> formulas =
                getSequentFormulas ( antec,
                                     !lastIfFormula || p_alreadyMatchedNewFor );
            final IfMatchResult mr = getTaclet ().matchIf ( formulas.iterator (),
                                                            p_ifSeqTail.head ().formula (),
                                                            p_matchCond,
                                                            getServices () );

            // For each matching formula call the method again to match
            // the remaining terms
            Iterator<IfFormulaInstantiation> itCand = mr.getFormulas        ().iterator ();
            Iterator<MatchConditions>        itMC   = mr.getMatchConditions ().iterator ();
            p_ifSeqTail                             = p_ifSeqTail.tail ();
            while ( itCand.hasNext () ) {
                final IfFormulaInstantiation ifInstantiation = itCand.next ();
                final boolean nextAlreadyMatchedNewFor = lastIfFormula
                                         || p_alreadyMatchedNewFor
                                         || isNewFormula ( ifInstantiation );
                findIfFormulaInstantiationsHelp ( p_ifSeqTail,
                                                  p_ifSeqTail2nd,
                                                  p_alreadyMatched.prepend ( ifInstantiation ),
                                                  itMC.next (),
                                                  nextAlreadyMatchedNewFor );
            }
        }

        private Proof getProof () {
            return goal.proof();
        }

        private Services getServices () {
            return getProof ().getServices();
        }

        private NoPosTacletApp setAllInstantiations ( MatchConditions p_matchCond, ImmutableList<IfFormulaInstantiation> p_alreadyMatched ) {
            return NoPosTacletApp.createNoPosTacletApp(
        	    getTaclet(),
                    p_matchCond.getInstantiations(),
                    p_alreadyMatched,
                    getServices());
        }

        private ImmutableList<SequentFormula> createSemisequentList ( Semisequent p_ss ) {
            ImmutableList<SequentFormula> res = ImmutableSLList.<SequentFormula>nil();

            for (final SequentFormula cf : p_ss) {
                res = res.prepend ( cf );
            }
            return res;
        }

        /**
         * @return Returns the results.
         */
        public ImmutableList<TacletApp> getResults () {
            return results;
        }
    }


    /**
     * Direct-mapped cache of lists of formulas (potential instantiations of
     * if-formulas of taclets) that were modified after a certain point of time
     */

    /**
     * Hashmaps of the particular lists of formulas; the keys of the maps
     * is the point of time that separates old from new (modified) formulas
     *
     * Keys: Long        Values: IList<IfFormulaInstantiation>
     */
    protected static final class IfInstCache {
        public Node cacheKey = null;

        public final HashMap<Long, ImmutableList<IfFormulaInstantiation>> 
            antecCache = new LinkedHashMap<Long, ImmutableList<IfFormulaInstantiation>> ();
        public final HashMap<Long, ImmutableList<IfFormulaInstantiation>>  succCache  = 
            new LinkedHashMap<Long, ImmutableList<IfFormulaInstantiation>>  ();  
        public void reset(Node n){
            cacheKey = n;
            antecCache.clear ();
            succCache.clear ();
        }
    }

    /**This field causes a memory leak (that is ad-hoc-ly fixed in
     * QueueRuleApplicationManager.clearCache()) because it is static and it
     * has a reference to node which has again a reference to proof.
     * Can this field be made non-static by putting it in some other class?
     * This field was private before the fix*/
    public static final IfInstCache ifInstCache = new IfInstCache ();
}
