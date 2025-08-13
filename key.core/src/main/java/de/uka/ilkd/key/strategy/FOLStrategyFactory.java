/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

import org.jspecify.annotations.NonNull;

public class FOLStrategyFactory implements StrategyFactory {
    public static final String TOOL_TIP_QUANTIFIER_NONE =
        "<html>" + "Do not instantiate quantified formulas automatically" + "</html>";
    public static final String TOOL_TIP_QUANTIFIER_NO_SPLITS = "<html>"
        + "Instantiate quantified formulas automatically<br>"
        + "with terms that occur in a sequent, but only if<br>"
        + "this does not cause proof splitting. Further, quantified<br>"
        + "formulas that contain queries are not instantiated<br>" + "automatically." + "</html>";
    public static final String TOOL_TIP_QUANTIFIER_NO_SPLITS_WITH_PROGS =
        "<html>" + "Instantiate quantified formulas automatically<br>"
            + "with terms that occur in a sequent, but if the<br>"
            + "sequent contains programs then only perform<br>"
            + "instantiations that do not cause proof splitting.<br>"
            + "Further, quantified formulas that contain queries<br>"
            + "are not instantiated automatically." + "</html>";
    public static final String TOOL_TIP_QUANTIFIER_FREE =
        "<html>" + "Instantiate quantified formulas automatically<br>"
            + "with terms that occur in a sequent, also if this<br>"
            + "might cause proof splitting." + "</html>";

    @Override
    public Strategy<@NonNull Goal> create(Proof proof, StrategyProperties strategyProperties) {
        return new FOLStrategy(proof, strategyProperties);
    }

    private static OneOfStrategyPropertyDefinition getQuantifierTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
            "Quantifier treatment", 2,
            new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_NONE, "None",
                TOOL_TIP_QUANTIFIER_NONE, 2, 4),
            new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_NON_SPLITTING,
                "No Splits", TOOL_TIP_QUANTIFIER_NO_SPLITS, 6, 2),
            new StrategyPropertyValueDefinition(
                StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS, "No Splits with Progs",
                TOOL_TIP_QUANTIFIER_NO_SPLITS_WITH_PROGS, 2, 4),
            new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_INSTANTIATE, "Free",
                TOOL_TIP_QUANTIFIER_FREE, 6, 2));
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        final OneOfStrategyPropertyDefinition quantifierTreatment = getQuantifierTreatment();
        return new StrategySettingsDefinition("FOL Options", quantifierTreatment);
    }

    @Override
    public Name name() {
        return FOLStrategy.NAME;
    }
}
