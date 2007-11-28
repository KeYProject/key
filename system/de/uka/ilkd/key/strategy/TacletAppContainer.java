// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import java.util.HashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SetOfSchemaVariable;
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

    private ListOfTacletApp incMatchIfFormulas (Goal p_goal) {
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
    public ListOfRuleAppContainer createFurtherApps (Goal p_goal,
                                                     Strategy p_strategy) {
        if ( !isStillApplicable ( p_goal )
             ||
             getTacletApp ().ifInstsComplete ()
             && !ifFormulasStillValid ( p_goal ))
            return SLListOfRuleAppContainer.EMPTY_LIST;

        final TacletAppContainer newCont = createContainer ( p_goal, p_strategy );
        if ( newCont.getCost () instanceof TopRuleAppCost )
            return SLListOfRuleAppContainer.EMPTY_LIST;

        ListOfRuleAppContainer res =
            SLListOfRuleAppContainer.EMPTY_LIST.prepend ( newCont );

        if ( getTacletApp ().ifInstsComplete () ) {
            res = addInstances ( getTacletApp (), res, p_goal, p_strategy );            
        } else {
            final IteratorOfTacletApp it =
                incMatchIfFormulas ( p_goal ).iterator ();
            while ( it.hasNext () ) {
                final TacletApp app = it.next ();
                res = addContainer ( app, res, p_goal, p_strategy );
                res = addInstances ( app, res, p_goal, p_strategy );
            }
        }
        
        return res;
    }


    /**
     * Add all instances of the given taclet app (that are possibly produced
     * using method <code>instantiateApp</code> of the strategy) to
     * <code>targetList</code>
     */
    private ListOfRuleAppContainer addInstances( TacletApp app,
                                                 ListOfRuleAppContainer targetList,
                                                 Goal p_goal,
                                                 Strategy p_strategy) {
        if ( app.uninstantiatedVars ().size () == 0 ) return targetList;
        return instantiateApp ( app, targetList, p_goal, p_strategy );
    }

    /**
     * Use the method <code>instantiateApp</code> of the strategy for choosing
     * the values of schema variables that have not been instantiated so far
     */
    private ListOfRuleAppContainer instantiateApp(TacletApp app,
                                                  ListOfRuleAppContainer targetList,
                                                  final Goal p_goal,
                                                  Strategy p_strategy) {
        // just for being able to modify the result-list in an
        // anonymous class
        final ListOfRuleAppContainer[] resA =
            new ListOfRuleAppContainer[] { targetList };
        
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
    private ListOfRuleAppContainer addContainer(TacletApp app,
                                                ListOfRuleAppContainer targetList,
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
    private ListOfRuleAppContainer addContainer(TacletApp app,
                                                ListOfRuleAppContainer targetList,
                                                Goal p_goal,
                                                RuleAppCost cost) {
        if ( !sufficientlyCompleteApp ( app ) ) return targetList;
        return targetList.prepend ( TacletAppContainer
                                    .createContainer ( app,
                                                       getPosInOccurrence ( p_goal ),
                                                       p_goal,
                                                       cost,
                                                       false ) );
    }

    private boolean sufficientlyCompleteApp(TacletApp app) {
        final SetOfSchemaVariable needed = app.neededUninstantiatedVars ();
        if ( needed.size () == 0 ) return true;
        final IteratorOfSchemaVariable it = needed.iterator ();
        while ( it.hasNext () ) {
            final SchemaVariable sv = it.next ();
            if ( sv.isSkolemTermSV () ) continue;
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
    static ListOfRuleAppContainer createAppContainers
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
    static ListOfRuleAppContainer createAppContainers
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
        return SLListOfRuleAppContainer.EMPTY_LIST
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

    	final IteratorOfIfFormulaInstantiation it =
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
            app = app.setPosInOccurrence ( pio );
            if ( app == null ) return null;
        }
    
        if ( !app.complete() )
            app = app.tryToInstantiate ( p_goal, p_goal.proof().getServices() );
    
        return app;
    }
    
    /**
     * This class implements custom instantiation of if-formulas.
     */
    private class IfInstantiator {
        private final Goal      goal;
        
        private ListOfIfFormulaInstantiation allAntecFormulas;
        private ListOfIfFormulaInstantiation allSuccFormulas;

        private ListOfTacletApp results = SLListOfTacletApp.EMPTY_LIST;
        
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
         * @return a list of tacletapps with the found if formula
         * instantiations
         */
        public void findIfFormulaInstantiations () {
            final Sequent p_seq = goal.sequent();

            Debug.assertTrue ( getTacletApp().ifFormulaInstantiations() == null,
                   "The if formulas have already been instantiated" );

            if ( getTaclet ().ifSequent () == Sequent.EMPTY_SEQUENT )
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
                      SLListOfIfFormulaInstantiation.EMPTY_LIST,
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
        private ListOfIfFormulaInstantiation getSequentFormulas ( boolean p_antec,
                                                                  boolean p_all ) {
            if ( p_all ) return getAllSequentFormulas ( p_antec );

            final ListOfIfFormulaInstantiation cache =
                getNewSequentFormulasFromCache(p_antec);
            if ( cache != null ) return cache;

            final ListOfIfFormulaInstantiation newFormulas =
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
        private ListOfIfFormulaInstantiation selectNewFormulas (boolean p_antec) {
            final IteratorOfIfFormulaInstantiation it =
                getAllSequentFormulas ( p_antec ).iterator ();                                                                
            ListOfIfFormulaInstantiation res =
                SLListOfIfFormulaInstantiation.EMPTY_LIST;

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

            final ListOfIfFormulaInstantiation cache =
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

            final ConstrainedFormula cfma = p_ifInstantiation.getConstrainedFormula ();
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

        private ListOfIfFormulaInstantiation
                    getNewSequentFormulasFromCache (boolean p_antec) {
            synchronized ( ifInstCache ) {
                if ( ifInstCache.cacheKey != goal.node () ) return null;

                // the cache contains formula lists for the right semisequent
                return (ListOfIfFormulaInstantiation)
                            getCacheMap ( p_antec ).get ( getAgeObject () );
            }
        }

        private void addNewSequentFormulasToCache (ListOfIfFormulaInstantiation p_list,
                                                   boolean p_antec) {
            synchronized ( ifInstCache ) {
                if ( ifInstCache.cacheKey != goal.node () ) {
                    ifInstCache.cacheKey = goal.node ();
                    ifInstCache.antecCache.clear ();
                    ifInstCache.succCache.clear ();
                }

                getCacheMap ( p_antec ).put ( getAgeObject (), p_list );
            }
        }


        private HashMap getCacheMap (boolean p_antec) {
            return p_antec ? ifInstCache.antecCache : ifInstCache.succCache;
        }

        private Long getAgeObject () {
            return new Long ( getAge() );
        }


        private ListOfIfFormulaInstantiation getAllSequentFormulas ( boolean p_antec ) {
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
         * @param p_toMatch
         *            list of the formulas to match the current if semisequent
         *            formulas with
         * @param p_toMatch2nd
         *            list of the formulas of the antecedent
         */
        private void findIfFormulaInstantiationsHelp
            ( ListOfConstrainedFormula      p_ifSeqTail,
              ListOfConstrainedFormula      p_ifSeqTail2nd,
              ListOfIfFormulaInstantiation  p_alreadyMatched,
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
            final ListOfIfFormulaInstantiation formulas =
                getSequentFormulas ( antec,
                                     !lastIfFormula || p_alreadyMatchedNewFor );
            final IfMatchResult mr = getTaclet ().matchIf ( formulas.iterator (),
                                                            p_ifSeqTail.head ().formula (),
                                                            p_matchCond,
                                                            getServices (),
                                                            getUserConstraint () );

            // For each matching formula call the method again to match
            // the remaining terms
            IteratorOfIfFormulaInstantiation itCand = mr.getFormulas        ().iterator ();
            IteratorOfMatchConditions        itMC   = mr.getMatchConditions ().iterator ();
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

        private Constraint getUserConstraint () {
            return getProof ().getUserConstraint().getConstraint();
        }

        private Proof getProof () {
            return goal.proof();
        }

        private Services getServices () {
            return getProof ().getServices();
        }

        private NoPosTacletApp setAllInstantiations ( MatchConditions p_matchCond, ListOfIfFormulaInstantiation p_alreadyMatched ) {
            return NoPosTacletApp.createNoPosTacletApp(getTaclet(),
                    p_matchCond.getInstantiations(), p_matchCond.getConstraint(),
                    p_matchCond.getNewMetavariables(), p_alreadyMatched);
        }

        private ListOfConstrainedFormula createSemisequentList ( Semisequent p_ss ) {
            ListOfConstrainedFormula res = SLListOfConstrainedFormula.EMPTY_LIST;

            IteratorOfConstrainedFormula it  = p_ss.iterator ();
            while ( it.hasNext () )
                res = res.prepend ( it.next () );

            return res; 
        }

        /**
         * @return Returns the results.
         */
        public ListOfTacletApp getResults () {
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
     * Keys: Long        Values: ListOfIfFormulaInstantiation
     */
    protected static final class IfInstCache {
        public Node cacheKey = null;

        public final HashMap antecCache = new HashMap ();
        public final HashMap succCache  = new HashMap ();               
    }

    protected static final IfInstCache ifInstCache = new IfInstCache ();
}
