package de.uka.ilkd.key.strategy;

import java.util.HashMap;
import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.FormulaTagManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.IfFormulaInstSeq;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.IfMatchResult;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;
import static de.uka.ilkd.key.strategy.IfInstantiationCache.ifInstCache;

/**
 * This class implements custom instantiation of if-formulas.
 */
public class IfInstantiator {
    private final Goal      goal;

    private ImmutableList<IfFormulaInstantiation> allAntecFormulas;
    private ImmutableList<IfFormulaInstantiation> allSuccFormulas;

    private ImmutableList<TacletApp> results = ImmutableSLList.<TacletApp>nil();
    
    private final TacletAppContainer tacletAppContainer;

    IfInstantiator (TacletAppContainer tacletAppContainer, final Goal goal ) {
        this.goal = goal;
        this.tacletAppContainer = tacletAppContainer;
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

        Debug.assertTrue ( tacletAppContainer.getTacletApp().ifFormulaInstantiations() == null,
               "The if formulas have already been instantiated" );

        if ( getTaclet ().ifSequent ().isEmpty() )
            addResult ( tacletAppContainer.getTacletApp () );
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
                  tacletAppContainer.getTacletApp ().matchConditions (),
                  false );
        }
    }


    private Taclet getTaclet () {
        return tacletAppContainer.getTacletApp ().taclet ();
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
                                                          PosInTerm.getTopLevel(),
                                                          antec );

        final FormulaTagManager tagManager = goal.getFormulaTagManager ();

        final FormulaTag tag = tagManager.getTagForPos ( pio );
        final long formulaAge = tagManager.getAgeForTag ( tag );

        // The strict relation can be used, because when applying a rule the
        // age of a goal is increased before the actual modification of the
        // goal take place
        return tacletAppContainer.getAge () < formulaAge;
    }

    private ImmutableList<IfFormulaInstantiation>
                getNewSequentFormulasFromCache (boolean p_antec) {
        synchronized ( ifInstCache ) {
            if ( ifInstCache.cacheKey != goal.node () ) return null;

            // the cache contains formula lists for the right semisequent
            return getCacheMap ( p_antec ).get ( tacletAppContainer.getAge () );
        }
    }

    private void addNewSequentFormulasToCache (ImmutableList<IfFormulaInstantiation> p_list,
                                               boolean p_antec) {
        synchronized ( ifInstCache ) {
            if ( ifInstCache.cacheKey != goal.node () ) {
                ifInstCache.reset(goal.node());
            }

            getCacheMap ( p_antec ).put ( tacletAppContainer.getAge (), p_list );
        }
    }

    private HashMap<Long, ImmutableList<IfFormulaInstantiation>> getCacheMap (boolean p_antec) {
        return p_antec ? ifInstCache.antecCache : ifInstCache.succCache;
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
        final IfMatchResult mr = getTaclet ().getMatcher().matchIf(formulas, p_ifSeqTail.head ().formula (), p_matchCond, getServices ());

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