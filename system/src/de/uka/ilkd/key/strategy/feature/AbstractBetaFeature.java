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

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.util.LRUCache;


/**
 * This abstract class contains some auxiliary methods for the selection of
 * beta rules that are supposed to be applied. Used terminology is defined in
 * Diss. by Martin Giese.
 */
public abstract class AbstractBetaFeature implements Feature {

    /*
     * Table of formulas which could be splitted using the beta rule
     * This is the cache the method "isBetaCandidate" uses
     *
     *    keys: Term              values: TermInfo
     */
    private static LRUCache<Term, TermInfo> betaCandidates = new LRUCache<Term, TermInfo> (1000);

    /** helper for computing maxPosPath_* in TermInfo */
    private static MaxPosPathHelper maxPosPathHelper = new MaxPosPathHelper();

    /** helper for computing maxDPath_* in TermInfo */
    private static MaxDPathHelper maxDPathHelper = new MaxDPathHelper();
    
    /**
     * Get the informations about a term
     */
    private static TermInfo termInfo (Term p_t) {
        TermInfo ti;
        synchronized ( betaCandidates ) {
            ti = betaCandidates.get ( p_t );
        }

        if ( ti == null ) {
            ti = new TermInfo ();

            ti.purePosPath_positive = hasPurePosPathHelp ( p_t, true );
            ti.purePosPath_negative = hasPurePosPathHelp ( p_t, false );

            ti.maxPosPath_positive = maxPosPathHelp ( p_t, true );
            ti.maxPosPath_negative = maxPosPathHelp ( p_t, false );

            ti.maxDPath_positive = maxDPathHelp ( p_t, true );
            ti.maxDPath_negative = maxDPathHelp ( p_t, false );

            ti.containsNegAtom_positive = containsNegAtomHelp ( p_t, true );
            ti.containsNegAtom_negative = containsNegAtomHelp ( p_t, false );

            ti.containsQuantifier = containsQuantifierHelp ( p_t );

            ti.candidate = candidateHelp ( p_t, ti );

            synchronized ( betaCandidates ) {
                betaCandidates.put ( p_t, ti );
            }
        }

        return ti;
    }
    
    private abstract static class MaxPathHelper {
        public int compute(Term p_t, boolean p_positive) {
            if ( p_t.op () == ( p_positive ? Junctor.AND : Junctor.OR ) )
                return compute ( p_t.sub ( 0 ), p_positive )
                       + compute ( p_t.sub ( 1 ), p_positive );

            else if ( p_t.op () == ( p_positive ? Junctor.OR : Junctor.AND ) )
                return Math.max ( compute ( p_t.sub ( 0 ), p_positive ),
                                  compute ( p_t.sub ( 1 ), p_positive ) );

            else if ( p_t.op () == Junctor.NOT )
                return compute ( p_t.sub ( 0 ), !p_positive );

            else if ( p_positive && p_t.op () == Junctor.IMP )
                return Math.max ( compute ( p_t.sub ( 0 ), !p_positive ),
                                  compute ( p_t.sub ( 1 ), p_positive ) );

            else if ( !p_positive && p_t.op () == Junctor.IMP )
                return compute ( p_t.sub ( 0 ), !p_positive )
                       + compute ( p_t.sub ( 1 ), p_positive );

            else if ( p_positive && p_t.op () == Equality.EQV )
                return Math.max ( compute ( p_t.sub ( 0 ), p_positive )
                                  + compute ( p_t.sub ( 1 ), p_positive ),
                                  compute ( p_t.sub ( 0 ), !p_positive )
                                  + compute ( p_t.sub ( 1 ), !p_positive ) );

            else if ( !p_positive && p_t.op () == Equality.EQV )
                return Math.max ( compute ( p_t.sub ( 0 ), !p_positive )
                                  + compute ( p_t.sub ( 1 ), p_positive ),
                                  compute ( p_t.sub ( 0 ), p_positive )
                                  + compute ( p_t.sub ( 1 ), !p_positive ) );

            return computeDefault(p_t, p_positive);
        }
        
        protected abstract int computeDefault(Term p_t, boolean p_positive);
    }
    
    private static class MaxPosPathHelper extends MaxPathHelper {
        protected int computeDefault(Term p_t, boolean p_positive) {
            if ( alwaysReplace ( p_t ) ) return 1;

            return p_positive ? 0 : 1;
        }
    }

    private static class MaxDPathHelper extends MaxPathHelper {
        protected int computeDefault(Term p_t, boolean p_positive) {
            return 1;
        }
    }
    
    private static int maxPosPathHelp (Term p_t, boolean p_positive) {
        return maxPosPathHelper.compute(p_t, p_positive);
    }

    private static int maxDPathHelp (Term p_t, boolean p_positive) {
        return maxDPathHelper.compute(p_t, p_positive);
    }

    /**
     * TODO: It would be nice to integrate this with the framework for
     * computing maxPosPath/maxDPath, however different return types pose
     * a problem. Perhaps this could be solved using generics? 
     */
    private static boolean hasPurePosPathHelp (Term p_t, boolean p_positive) {
        if ( p_t.op () == ( p_positive ? Junctor.AND : Junctor.OR ) )
            return hasPurePosPath ( p_t.sub ( 0 ), p_positive )
                   && hasPurePosPath ( p_t.sub ( 1 ), p_positive );

        else if ( p_t.op () == ( p_positive ? Junctor.OR : Junctor.AND ) )
            return hasPurePosPath ( p_t.sub ( 0 ), p_positive )
                   || hasPurePosPath ( p_t.sub ( 1 ), p_positive );

        else if ( p_t.op () == Junctor.NOT )
            return hasPurePosPath ( p_t.sub ( 0 ), !p_positive );

        else if ( p_positive && p_t.op () == Junctor.IMP )
            return hasPurePosPath ( p_t.sub ( 0 ), !p_positive )
                   || hasPurePosPath ( p_t.sub ( 1 ), p_positive );

        else if ( !p_positive && p_t.op () == Junctor.IMP )
            return hasPurePosPath ( p_t.sub ( 0 ), !p_positive )
                   && hasPurePosPath ( p_t.sub ( 1 ), p_positive );

        else if ( p_positive && p_t.op () == Equality.EQV )
            return ( hasPurePosPath ( p_t.sub ( 0 ), p_positive ) &&
                     hasPurePosPath ( p_t.sub ( 1 ), p_positive ) )
                   || ( hasPurePosPath ( p_t.sub ( 0 ), !p_positive ) &&
                        hasPurePosPath ( p_t.sub ( 1 ), !p_positive ) );

        else if ( !p_positive && p_t.op () == Equality.EQV )
            return ( hasPurePosPath ( p_t.sub ( 0 ), !p_positive ) &&
                     hasPurePosPath ( p_t.sub ( 1 ), p_positive ) )
                   || ( hasPurePosPath ( p_t.sub ( 0 ), p_positive ) &&
                        hasPurePosPath ( p_t.sub ( 1 ), !p_positive ) );

        else if ( alwaysReplace ( p_t ) ) return true;

        return !p_positive;
    }

    private static boolean containsNegAtomHelp (Term p_t, boolean p_positive) {
        if ( p_t.op () == Junctor.AND || p_t.op () == Junctor.OR )
            return containsNegAtom ( p_t.sub ( 0 ), p_positive )
                   || containsNegAtom ( p_t.sub ( 1 ), p_positive );

        else if ( p_t.op () == Junctor.NOT )
            return containsNegAtom ( p_t.sub ( 0 ), !p_positive );

        else if ( p_t.op () == Junctor.IMP )
            return containsNegAtom ( p_t.sub ( 0 ), !p_positive )
                   || containsNegAtom ( p_t.sub ( 1 ), p_positive );

        else if ( p_t.op () == Equality.EQV || alwaysReplace ( p_t ) )
            return true;

        return !p_positive;
    }

    private static boolean containsQuantifierHelp (Term p_t) {
        if ( p_t.op () == Junctor.AND || p_t.op () == Junctor.OR || p_t.op () == Junctor.IMP
             || p_t.op () == Equality.EQV )
            return containsQuantifier ( p_t.sub ( 0 ) )
                   || containsQuantifier ( p_t.sub ( 1 ) );
        else if ( p_t.op () == Junctor.NOT )
            return containsQuantifier ( p_t.sub ( 0 ) );
        else
            return alwaysReplace ( p_t );
    }

    private static Object candidateHelp (Term p_t, TermInfo p_ti) {
        if ( p_t.op () == Junctor.IMP || p_t.op () == Junctor.OR )
            return isBetaCandidateHelp ( p_ti, false ) ? TermInfo.CAND_LEFT
                                                      : TermInfo.CAND_NEVER;
        else if ( p_t.op () == Junctor.AND )
            return isBetaCandidateHelp ( p_ti, true ) ? TermInfo.CAND_RIGHT
                                                     : TermInfo.CAND_NEVER;
        else if ( p_t.op () == Equality.EQV ) {
            if ( isBetaCandidateHelp ( p_ti, true ) )
                return isBetaCandidateHelp ( p_ti, false ) ? TermInfo.CAND_BOTH
                                                          : TermInfo.CAND_RIGHT;
            else
                return isBetaCandidateHelp ( p_ti, false ) ? TermInfo.CAND_LEFT
                                                          : TermInfo.CAND_NEVER;
        }

        return TermInfo.CAND_NEVER;
    }

    private static boolean isBetaCandidateHelp (TermInfo p_ti, boolean p_positive) {
/*        return p_ti.containsQuantifier
            || ( p_positive ? p_ti.purePosPath_positive
                            : p_ti.purePosPath_negative ); */
        return p_ti.containsQuantifier
            || ( p_positive ? p_ti.maxPosPath_positive
                            : p_ti.maxPosPath_negative ) > 1;
    }

    /**
     * p_t contains a d-path consisting only of positive literals (as a formula
     * of the antecedent)
     */
    protected static boolean hasPurePosPath (Term p_t, boolean p_positive) {
        TermInfo ti = termInfo ( p_t );
        return p_positive ? ti.purePosPath_positive : ti.purePosPath_negative;
    }

    /**
     * The maximal number of positive literals occurring within a
     * d-path of "p_t" as a formula of the antecedent
     */
    protected static int maxPosPath (Term p_t, boolean p_positive) {
        TermInfo ti = termInfo ( p_t );
        return p_positive ? ti.maxPosPath_positive : ti.maxPosPath_negative;
    }

    /**
     * The length (number of literals) of the maximum d-path of the given
     * formula as a formula of the antecedent
     */
    protected static int maxDPath (Term p_t, boolean p_positive) {
        TermInfo ti = termInfo ( p_t );
        return p_positive ? ti.maxDPath_positive : ti.maxDPath_negative;
    }

    /**
     * @return true iff "p_t" contains a quantifier or a modality
     */
    protected static boolean containsQuantifier (Term p_t) {
        TermInfo ti = termInfo ( p_t );
        return ti.containsQuantifier;
    }

    /**
    * @return true iff the given
    * formula contains a negated atom as a formula of the antecedent
     */
    protected static boolean containsNegAtom (Term p_t, boolean p_positive) {
        TermInfo ti = termInfo ( p_t );
        return p_positive ? ti.containsNegAtom_positive : ti.containsNegAtom_negative;
    }

    /**
     * @return true iff the sign of "p_t" is not relevant (quantifiers
     * etc. could be positive or negative)
     */
    public static boolean alwaysReplace (Term p_t) {
        return p_t.op () instanceof Modality || p_t.op () instanceof Quantifier;
    }

    /**
     * @return true iff the formula p_t could be splitted using the
     * beta rule
     */
    protected static boolean isBetaCandidate (Term p_t, boolean p_inAntec) {
        TermInfo ti = termInfo ( p_t );
        return ti.candidate == TermInfo.CAND_BOTH
               || ti.candidate == ( p_inAntec ? TermInfo.CAND_LEFT
                                             : TermInfo.CAND_RIGHT );
    }

    /**
     * Informations about a term as cached within "betaCandidates"
     */
    private static class TermInfo {

        public static final Integer CAND_NEVER = Integer.valueOf ( 0 );
        public static final Integer CAND_LEFT  = Integer.valueOf ( 1 );
        public static final Integer CAND_RIGHT = Integer.valueOf ( 2 );
        public static final Integer CAND_BOTH  = Integer.valueOf ( 3 );

        /** formula is positive (not negated) */
        public int                  maxPosPath_positive;

        public boolean              purePosPath_positive;

        // length of the maximum d-path
        public int                  maxDPath_positive;
        
        /** formula contains a negative atom */
        public boolean              containsNegAtom_positive;

        /** formula is negated */
        public int                  maxPosPath_negative;

        public boolean              purePosPath_negative;

        // length of the maximum d-path
        public int                  maxDPath_negative;

        /** formula contains a negative atom */
        public boolean              containsNegAtom_negative;

        /** formula contains a quantifier or modality */
        public boolean              containsQuantifier;

        /** one of CAND_* */
        public Object               candidate;
    }

    /**
     * Compute the cost of a RuleApp.
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return the cost of <code>app</code>
     */
    public RuleAppCost compute (RuleApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";
    
        final Term findTerm = pos.constrainedFormula ().formula ();
        
        return doComputation ( pos, findTerm );
    }

    protected abstract RuleAppCost doComputation (PosInOccurrence pos,
                                                  Term findTerm);

    public static void clearCache(){
        betaCandidates.clear();
    }
}
