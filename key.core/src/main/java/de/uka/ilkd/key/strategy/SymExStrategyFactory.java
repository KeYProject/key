/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

/// Creates [SymExStrategy]. Handles strategy settings for symbolic execution.
public class SymExStrategyFactory implements StrategyFactory {
    public static final String TOOL_TIP_LOOP_INVARIANT =
        "<html>" + "Use loop invariants for loops.<br>" + "Three properties have to be shown:<br>"
            + "<ul><li>Validity of invariant of a loop is preserved by the<br>"
            + "loop guard and loop body (initially valid).</li>"
            + "<li>If the invariant was valid at the start of the loop, it holds <br>"
            + "after arbitrarily many loop iterations (body preserves invariant).</li>"
            + "<li>Invariant holds after the loop terminates (use case).</li>" + "</ul></html>";
    public static final String TOOL_TIP_LOOP_SCOPE_INVARIANT_TACLET =
        "<html>" + "Use the loop scope-based invariant taclet, i.e. not the built-in rules.<br>"
            + "Three properties have to be shown:<br>"
            + "<ul><li>Validity of invariant of a loop is preserved by the<br>"
            + "loop guard and loop body (initially valid).</li>"
            + "<li>If the invariant was valid at the start of the loop, it holds <br>"
            + "after arbitrarily many loop iterations (body preserves invariant).</li>"
            + "<li>Invariant holds after the loop terminates (use case).</li>" + "</ul>"
            + "<p>The last two are combined into a single goal or split into two<br>"
            + "goals based on the 'javaLoopTreatment' strategy option.</p>" + "</html>";
    public static final String TOOL_TIP_LOOP_SCOPE_EXPAND =
        "<html>" + "Unroll loop body, but with the loop scope technology.<br>"
            + "This requires less program transformation for irregular<br>"
            + "termination behavior." + "</html>";
    public static final String TOOL_TIP_LOOP_EXPAND = "<html>" + "Unroll loop body." + "</html>";
    public static final String TOOL_TIP_LOOP_NONE = "<html>" + "Leave loops untouched." + "</html>";
    public static final String TOOL_TIP_BLOCK_CONTRACT_INTERNAL = "<html>"
        + "Java blocks are replaced by their contracts.<br>" + "Three properties are shown:"
        + "<ul><li>Validity of block contract in the method context</li>"
        + "<li>Precondition of contract holds</li>"
        + "<li>Postcondition holds after block terminates</li>" + "</ul>" + "</html>";
    public static final String TOOL_TIP_BLOCK_CONTRACT_EXTERNAL =
        "<html>" + "Java blocks are replaced by their contracts.<br>" + "Two properties are shown:"
            + "<ul><li>Precondition of contract holds</li>"
            + "<li>Postcondition holds after block terminates</li>" + "</ul></html>";
    public static final String TOOL_TIP_BLOCK_EXPAND =
        "<html>" + "Do not use block contracts for Java blocks. Expand Java blocks." + "</html>";
    public static final String TOOL_TIP_METHOD_CONTRACT =
        "<html>Replace method calls by contracts. In some cases<br>"
            + "a method call may also be replaced by its method body.<br>"
            + "If query treatment is activated, this behavior applies<br>"
            + "to queries as well.</html>";
    public static final String TOOL_TIP_METHOD_EXPAND =
        "<html>Replace method calls by their bodies, i.e. by their<br>"
            + "implementation. Method contracts are strictly deactivated.</html>";
    public static final String TOOL_TIP_METHOD_NONE =
        "<html>" + "Stop when encountering a method" + "</html>";
    public static final String TOOL_TIP_MPS_MERGE =
        "<html>Use merge point statements for merging. That is,<br>"
            + "whenever all branches with a given merge point statement<br>"
            + "have reached it, the strategies will eventually merge<br>"
            + "the branches together using the merge point specification.</html>";
    public static final String TOOL_TIP_MPS_SKIP =
        "<html>Simply removes (skips) the merge point statment;<br>"
            + "no state merging is applied.</html>";
    public static final String TOOL_TIP_MPS_NONE =
        "<html>" + "Stop when encountering a merge point statement" + "</html>";

    @Override
    public SymExStrategy create(Proof proof, StrategyProperties strategyProperties) {
        return new SymExStrategy(proof, strategyProperties);
    }

    private static OneOfStrategyPropertyDefinition getLoopTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.LOOP_OPTIONS_KEY,
            "Loop treatment", 2,
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_SCOPE_INV_TACLET,
                "Invariant (Loop Scope)", TOOL_TIP_LOOP_SCOPE_INVARIANT_TACLET),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_SCOPE_EXPAND,
                "Expand (Loop Scope)", TOOL_TIP_LOOP_SCOPE_EXPAND),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_INVARIANT,
                "Invariant (Transformation)", TOOL_TIP_LOOP_INVARIANT),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_EXPAND,
                "Expand (Transformation)", TOOL_TIP_LOOP_EXPAND),
            new StrategyPropertyValueDefinition(StrategyProperties.LOOP_NONE, "None",
                TOOL_TIP_LOOP_NONE));
    }

    private static OneOfStrategyPropertyDefinition getBlockTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.BLOCK_OPTIONS_KEY,
            "Block treatment", 1,
            new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_CONTRACT_INTERNAL,
                "Internal Contract", TOOL_TIP_BLOCK_CONTRACT_INTERNAL),
            new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_CONTRACT_EXTERNAL,
                "External Contract", TOOL_TIP_BLOCK_CONTRACT_EXTERNAL),
            new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_EXPAND, "Expand",
                TOOL_TIP_BLOCK_EXPAND));
    }

    private static OneOfStrategyPropertyDefinition getMethodTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.METHOD_OPTIONS_KEY,
            "Method treatment",
            new StrategyPropertyValueDefinition(StrategyProperties.METHOD_CONTRACT, "Contract",
                TOOL_TIP_METHOD_CONTRACT),
            new StrategyPropertyValueDefinition(StrategyProperties.METHOD_EXPAND, "Expand",
                TOOL_TIP_METHOD_EXPAND),
            new StrategyPropertyValueDefinition(StrategyProperties.METHOD_NONE, "None",
                TOOL_TIP_METHOD_NONE));
    }

    private static OneOfStrategyPropertyDefinition getMergePointStatementTreatment() {
        return new OneOfStrategyPropertyDefinition(StrategyProperties.MPS_OPTIONS_KEY,
            "Merge point statements",
            new StrategyPropertyValueDefinition(StrategyProperties.MPS_MERGE, "Merge",
                TOOL_TIP_MPS_MERGE),
            new StrategyPropertyValueDefinition(StrategyProperties.MPS_SKIP, "Skip",
                TOOL_TIP_MPS_SKIP),
            new StrategyPropertyValueDefinition(StrategyProperties.MPS_NONE, "None",
                TOOL_TIP_MPS_NONE));
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        final OneOfStrategyPropertyDefinition loopTreatment = getLoopTreatment();
        final OneOfStrategyPropertyDefinition blockTreatment = getBlockTreatment();
        final OneOfStrategyPropertyDefinition methodTreatment = getMethodTreatment();
        final OneOfStrategyPropertyDefinition mergePointStatementTreatment =
            getMergePointStatementTreatment();
        return new StrategySettingsDefinition("Symbolic Execution Options",
            loopTreatment, blockTreatment, methodTreatment, mergePointStatementTreatment);
    }

    @Override
    public Name name() {
        return SymExStrategy.NAME;
    }
}
