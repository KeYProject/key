/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature.findprefix;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.feature.BinaryTacletAppFeature;


/**
 * Feature for investigating whether some restrictions to the prefix of the find formula apply.
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

        public final boolean check(PosInOccurrence pio) {
            return checker.check(pio);
        }
    }

    public enum PositionModifier {
        // If the parent operator of the find term is an update application,
        // then change the position (on which the checkers are applied)
        // to the parent operator. Repeat until parent is no update
        // application.
        ALLOW_UPDATE_AS_PARENT(new RemoveParentUpdateModifier());

        /** wrapped modifier */
        private final Modifier modifier;


        PositionModifier(Modifier modifier) {
            this.modifier = modifier;
        }

        PosInOccurrence modifyPosistion(PosInOccurrence pos) {
            return modifier.modifyPosistion(pos);
        }
    }

    private final PrefixChecker[] prefixCheckers;
    private final PositionModifier[] positionModifiers;


    /**
     * Construct a feature that checks the prefix with the passed PrefixCheckers. Computes zero
     * costs, if all PrefixCheckers return true, otherwise computes top cost.
     *
     * @param prefixCheckers the PrefixCheckers to be used.
     */
    public FindPrefixRestrictionFeature(PrefixChecker... prefixCheckers) {
        this(new PositionModifier[0], prefixCheckers);
    }

    /**
     * Construct a feature that checks the prefix with the passed PrefixCheckers. Computes zero
     * costs, if all PrefixCheckers return true, otherwise computes top cost. Before the prefix
     * check all PositionModifiers are applied. This allows for instance to ignore prefixing
     * updates.
     *
     * @param positionModifier the PositionModifier to be applied.
     * @param prefixCheckers the PrefixCheckers to be used.
     */
    public FindPrefixRestrictionFeature(PositionModifier positionModifier,
            PrefixChecker... prefixCheckers) {
        this(new PositionModifier[] { positionModifier }, prefixCheckers);
    }

    /**
     * Construct a feature that checks the prefix with the passed PrefixCheckers. Computes zero
     * costs, if all PrefixCheckers return true, otherwise computes top cost. Before the prefix
     * check all PositionModifiers are applied. This allows for instance to ignore prefixing
     * updates.
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
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        // apply the position modifiers
        PosInOccurrence newPos = pos;
        for (PositionModifier positionModifier : positionModifiers) {
            newPos = positionModifier.modifyPosistion(newPos);
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
        // iterate through the prefix and let the prefix checkers do their work
        for (PrefixChecker prefixChecker : prefixCheckers) {
            if (!prefixChecker.check(pos)) {
                return false;
            }
        }
        return true;
    }
}
