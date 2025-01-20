/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.Strategy;

/**
 * This class captures a proof macro which is meant to fully automise KeY proof workflow.
 *
 * It is experimental.
 *
 * It performs the following steps:
 * <ol>
 * <li>Finish symbolic execution
 * <li>>Separate proof obligations" +
 * <li>Expand invariant definitions
 * <li>Try to close all proof obligations
 * </ol>
 *
 * @author mattias ulbrich
 */
public class TranscendentalFloatSMTMacro extends SequentialProofMacro {


    @Override
    public String getName() {
        return "Transcendentals";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getScriptCommandName() {
        return "transcendental";
    }


    @Override
    public String getDescription() {
        return "<html>TODO";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new FullAutoMacro(), new TranscendentalMacro() };
    }

    private static class FullAutoMacro extends StrategyProofMacro {

        @Override
        protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
            return proof.getActiveStrategy();
        }

        @Override
        public String getName() {
            return "auto";
        }

        @Override
        public String getCategory() {
            return "undefined";
        }

        @Override
        public String getDescription() {
            return "none";
        }
    }

    private static class TranscendentalMacro extends AbstractPropositionalExpansionMacro {

        private static final Set<String> ADMITTED_RULES = makeAdmitted();

        @Override
        protected Set<String> getAdmittedRuleNames() {
            return ADMITTED_RULES;
        }

        @Override
        protected boolean allowOSS() {
            return true;
        }

        @Override
        public String getName() {
            return "transcendental-internal";
        }

        @Override
        public String getDescription() {
            return "TODO!";
        }
    }

    private static Set<String> makeAdmitted() {
        Set<String> result = new HashSet<>();
        result.add("sinIsNaN");
        result.add("sineIsZero");
        result.add("sineRange");
        result.add("sineIsNaNAlt");
        result.add("sineRangeAlt");
        result.add("sinIsNotNaN");
        result.add("sinRange2");
        result.add("sinRange3");
        result.add("cosIsNaN");
        result.add("cosRange");
        result.add("cosIsNaNAlt");
        result.add("cosRangeAlt");
        result.add("cosIsNotNaN");
        result.add("cosRange2");
        result.add("asinIsNaN");
        result.add("asineIsZero");
        result.add("asineRange");
        result.add("acosIsNaN");
        result.add("acosRange");
        result.add("tanIsNaN");
        result.add("tanIsZero");
        result.add("atan2IsNaN");
        result.add("atan2Range");
        result.add("sqrtIsNaN");
        result.add("sqrtIsInfinite");
        result.add("sqrtIsZero");
        result.add("sqrtIsNotNaN");
        result.add("sqrtIsSmaller");
        result.add("powIsOne");
        result.add("powIsNotNaN");
        result.add("powIsNaN1");
        result.add("powIsNaN2");
        result.add("powIsInfinite1");
        result.add("powIsZero1");
        result.add("powIsNaN3");
        result.add("powIsZero2");
        result.add("powIsInfinite2");
        result.add("expIsNaN");
        result.add("expIsInfinite");
        result.add("expIsZero");
        result.add("atanIsNaN");
        result.add("atanIsZero");
        result.add("atanRange");
        result.add("niceFloat");
        result.add("niceDouble");
        return result;
    }
}
