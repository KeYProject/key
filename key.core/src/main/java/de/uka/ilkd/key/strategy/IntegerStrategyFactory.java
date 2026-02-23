/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

/// Factory for [IntegerStrategy]. Additionally, handles all strategy settings
/// relevant to integers.
public class IntegerStrategyFactory implements StrategyFactory {
    public static final String TOOL_TIP_ARITHMETIC_BASE = "<html>" + "Basic arithmetic support:"
        + "<ul>" + "<li>Simplification of polynomial expressions</li>"
        + "<li>Computation of Gr&ouml;bner Bases for polynomials in the antecedent</li>"
        + "<li>(Partial) Omega procedure for handling linear inequations</li>" + "</ul>"
        + "</html>";
    public static final String TOOL_TIP_ARITHMETIC_DEF_OPS =
        "<html>" + "Automatically expand defined symbols like:" + "<ul>"
            + "<li><tt>/</tt>, <tt>%</tt>, <tt>jdiv</tt>, <tt>jmod</tt>, ...</li>"
            + "<li><tt>int_RANGE</tt>, <tt>short_MIN</tt>, ...</li>"
            + "<li><tt>inInt</tt>, <tt>inByte</tt>, ...</li>"
            + "<li><tt>addJint</tt>, <tt>mulJshort</tt>, ...</li>" + "</ul>" + "</html>";
    public static final String TOOL_TIP_ARITHMETIC_MODEL_SEARCH = "<html>"
        + "Support for non-linear inequations and model search.<br>" + "In addition, this performs:"
        + "<ul>" + "<li>Multiplication of inequations with each other</li>"
        + "<li>Systematic case distinctions (cuts)</li>" + "</ul>"
        + "This method is guaranteed to find counterexamples for<br>"
        + "invalid goals that only contain polynomial (in)equations.<br>"
        + "Such counterexamples turn up as trivially unprovable goals.<br>"
        + "It is also able to prove many more valid goals involving<br>"
        + "(in)equations, but will in general not terminate on such goals." + "</html>";

    private static OneOfStrategyPropertyDefinition getArithmeticTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
            "Arithmetic treatment",
            new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_NONE, "Basic",
                TOOL_TIP_ARITHMETIC_BASE),
            new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_DEF_OPS, "DefOps",
                TOOL_TIP_ARITHMETIC_DEF_OPS),
            new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_COMPLETION,
                "Model Search", TOOL_TIP_ARITHMETIC_MODEL_SEARCH));
    }

    @Override
    public IntegerStrategy create(Proof proof, StrategyProperties strategyProperties) {
        return new IntegerStrategy(proof, strategyProperties);
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        final OneOfStrategyPropertyDefinition arithmeticTreatment = getArithmeticTreatment();
        return new StrategySettingsDefinition("Integer Options", arithmeticTreatment);
    }

    @Override
    public Name name() {
        return IntegerStrategy.NAME;
    }
}
