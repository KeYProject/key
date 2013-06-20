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
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.BinaryTacletAppFeature;


/**
 * Feature for investigating whether some restrictions to the prefix of the
 * find formula apply.
 *
 * @author christoph
 */
public class FindPrefixRestrictionFeature extends BinaryTacletAppFeature {

    public enum PrefixChecker {

        // checks, whether the position in occurrence is in the antecedent
        ANTEC(new AntecChecker()),
        // checks, whether the position in occurrence is in the succedent
        SUCC(new SuccChecker()),
        // checks, whether the position in occurrence has antecedent polarity
        ANTEC_POLARITY(AntecSuccPrefixChecker.ANTE_POLARITY_CHECKER),
        // checks, whether the position in occurrence has succedent polarity
        SUCC_POLARITY(AntecSuccPrefixChecker.SUCC_POLARITY_CHECKER),
        // checks, whether the position in occurrence is top level
        TOP_LEVEL(new TopLevelChecker());

        /** wrapped checker */
        private final Checker checker;


        PrefixChecker(Checker checker) {
            this.checker = checker;
        }

        public void initPrefixCheck(PosInOccurrence p_pos) {
            checker.initPrefixCheck(p_pos);
        }


        public void checkOperator(Operator op,
                                  PIOPathIterator it) {
            checker.checkOperator(op, it);
        }


        public boolean getResult() {
            return checker.getResult();
        }
    };

    public enum PositionModifier {
        // If the parent operator of the find term is an update application,
        // then change the position (on which the checkers are applied)
        // to the parent operator. Repeat until parent is no update
        // application.
        ALLOW_UPDATE_AS_PARENT(new RemoveParentUpdateModifier());

        /** wrapped modifier */
        private final Modifier modifier;


        private PositionModifier(Modifier modifier) {
            this.modifier = modifier;
        }

        PosInOccurrence modifyPosistion(PosInOccurrence pos) {
            return modifier.modifyPosistion(pos);
        }
    }

    private final PrefixChecker[] prefixCheckers;
    private final PositionModifier[] positionModifiers;



    /**
     * Construct a feature that checks the prefix with the passed
     * PrefixCheckers. Computes zero costs, if all PrefixCheckers return true,
     * otherwise computes top cost.
     * 
     * @param prefixCheckers the PrefixCheckers to be used.
     */
    public FindPrefixRestrictionFeature(PrefixChecker... prefixCheckers) {
        this(new PositionModifier[0], prefixCheckers);
    }

    /**
     * Construct a feature that checks the prefix with the passed
     * PrefixCheckers. Computes zero costs, if all PrefixCheckers return true,
     * otherwise computes top cost. Before the prefix check all
     * PositionModifiers are applied. This allows for instance to ignore
     * prefixing updates.
     *
     * @param positionModifier the PositionModifier to be applied.
     * @param prefixCheckers the PrefixCheckers to be used.
     */
    public FindPrefixRestrictionFeature(PositionModifier positionModifier,
                                        PrefixChecker... prefixCheckers) {
        this(new PositionModifier[]{positionModifier}, prefixCheckers);
    }

    /**
     * Construct a feature that checks the prefix with the passed
     * PrefixCheckers. Computes zero costs, if all PrefixCheckers return true,
     * otherwise computes top cost. Before the prefix check all
     * PositionModifiers are applied. This allows for instance to ignore
     * prefixing updates.
     *
     * @param positionModifiers the PositionModifiers to be applied.
     * @param prefixCheckers the PrefixCheckers to be used.
     */
    public FindPrefixRestrictionFeature(PositionModifier[] positionModifiers,
                                        PrefixChecker... prefixCheckers) {
        this.positionModifiers = positionModifiers;
        this.prefixCheckers = prefixCheckers;
    }

    @Override
    protected boolean filter(TacletApp app,
                             PosInOccurrence pos,
                             Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        // apply the position modifiers
        PosInOccurrence newPos = pos;
        for (PositionModifier positionModifier : positionModifiers) {
            newPos = positionModifier.modifyPosistion(pos);
        }

        // apply the prefix checkers
        return checkPrefix(newPos);
    }


    /**
     * Applies the PrefixCheckers.
     *
     * @param pos the PosInOccurrence to be checked.
     * @return true, if all PrefixCheckers return true
     */
    private boolean checkPrefix(PosInOccurrence pos) {
        // init prefix checkers
        for (PrefixChecker prefixChecker : prefixCheckers) {
            prefixChecker.initPrefixCheck(pos);
        }

        // iterate through the prefix and let the prefix checkers do their work
        if (pos.posInTerm() != null) {
            PIOPathIterator it = pos.iterator();
            Operator op;

            while (it.next() != -1) {
                final Term t = it.getSubTerm();
                op = t.op();

                for (PrefixChecker prefixChecker : prefixCheckers) {
                    prefixChecker.checkOperator(op, it);
                }

            }
        }

        // return the result
        boolean result = true;
        for (PrefixChecker prefixChecker : prefixCheckers) {
            result &= prefixChecker.getResult();
        }
        return result;
    }
}
