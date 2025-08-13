/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.AbstractStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

import org.jspecify.annotations.NonNull;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class ModularJavaDLStrategyFactory implements StrategyFactory {
    private final List<StrategyFactory> componentFactories = Arrays.asList(new FOLStrategyFactory(),
        new IntegerStrategyFactory(), new SymExStrategyFactory(), new StringStrategyFactory(),
        new JavaCardDLStrategyFactory());

    /**
     * The unique {@link Name} of this {@link StrategyFactory}.
     */
    public static final Name NAME = ModularJavaDLStrategy.NAME;

    public static final String TOOL_TIP_STOP_AT_DEFAULT =
        "<html>Stop when (i) the maximum number of rule<br>"
            + "applications is reached or (ii) no more rules are<br>"
            + "applicable on the proof tree.</html>";
    public static final String TOOL_TIP_STOP_AT_UNCLOSABLE =
        "<html>Stop as soon as the first not automatically<br>"
            + "closable goal is encountered.</html>";
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

    public ModularJavaDLStrategyFactory() {
    }

    public static final String toolTipUserOff(int i) {
        return "Taclets of the rule set \"userTaclets" + i + "\" are not applied automatically";
    }

    public static final String toolTipUserLow(int i) {
        return "Taclets of the rule set \"userTaclets" + i
            + "\" are applied automatically with low priority";
    }

    public static final String toolTipUserHigh(int i) {
        return "Taclets of the rule set \"userTaclets" + i
            + "\" are applied automatically with high priority";
    }

    private static OneOfStrategyPropertyDefinition getStopAt() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.STOPMODE_OPTIONS_KEY,
            "Stop at",
            new StrategyPropertyValueDefinition(StrategyProperties.STOPMODE_DEFAULT, "Default",
                TOOL_TIP_STOP_AT_DEFAULT),
            new StrategyPropertyValueDefinition(StrategyProperties.STOPMODE_NONCLOSE, "Unclosable",
                TOOL_TIP_STOP_AT_UNCLOSABLE));
    }

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

    private static OneOfStrategyPropertyDefinition getUserOptions() {
        // User properties
        List<AbstractStrategyPropertyDefinition> props = new LinkedList<>();
        for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
            OneOfStrategyPropertyDefinition user = new OneOfStrategyPropertyDefinition(
                StrategyProperties.userTacletsOptionsKey(i), i + ":  ",
                new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_OFF, "Off",
                    toolTipUserOff(i), 3, 1),
                new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_LOW,
                    "Low prior.", toolTipUserLow(i), 4, 2),
                new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_HIGH,
                    "High prior.", toolTipUserHigh(i), 6, 2));
            props.add(user);
        }

        return new OneOfStrategyPropertyDefinition(null, "User-specific taclet sets",
            "<html>" + "These options define whether user- and problem-specific taclet sets<br>"
                + "are applied automatically by the strategy. Problem-specific taclets<br>"
                + "can be defined in the \\rules-section of a .key-problem file. For<br>"
                + "automatic application, the taclets have to contain a clause<br>"
                + "\\heuristics(userTaclets1), \\heuristics(userTaclets2), etc." + "</html>",
            -1, props.toArray(new AbstractStrategyPropertyDefinition[0]));
    }

    @Override
    public Strategy<@NonNull Goal> create(Proof proof, StrategyProperties strategyProperties) {
        List<AbstractFeatureStrategy> componentStrategies = componentFactories.stream()
                .map(f -> (AbstractFeatureStrategy) f.create(proof, strategyProperties))
                .collect(Collectors.toList());
        return new ModularJavaDLStrategy(proof, componentStrategies, strategyProperties);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        // Properties
        final OneOfStrategyPropertyDefinition stopAt = getStopAt();
        final OneOfStrategyPropertyDefinition userOptions = getUserOptions();

        List<AbstractStrategyPropertyDefinition> componentSettings = componentFactories.stream()
                .flatMap(f -> f.getSettingsDefinition().getProperties().stream())
                .collect(Collectors.toCollection(ArrayList::new));
        componentSettings.addFirst(stopAt);
        componentSettings.add(userOptions);

        AbstractStrategyPropertyDefinition[] properties =
            componentSettings.toArray(new AbstractStrategyPropertyDefinition[0]);

        // Model
        return new StrategySettingsDefinition("JavaDL Options", properties);
    }
}
