/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.parser.builder.TacletPBuilder;
import org.key_project.rusty.rule.VariableCondition;
import org.key_project.rusty.rule.tacletbuilder.TacletBuilder;


/**
 * This class manages the register of various factories for the different built-in
 * {@link VariableCondition}s.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public class TacletBuilderManipulators {
    // region Factories
    // Shortcut for argument types
    // private static final ArgumentType TR = TYPE_RESOLVER;
    private static final ArgumentType KRT = ArgumentType.RUST_TYPE;
    private static final ArgumentType PV = ArgumentType.VARIABLE;
    private static final ArgumentType USV = ArgumentType.VARIABLE;
    private static final ArgumentType TSV = ArgumentType.VARIABLE;
    private static final ArgumentType ASV = ArgumentType.VARIABLE;
    private static final ArgumentType FSV = ArgumentType.VARIABLE;
    private static final ArgumentType SV = ArgumentType.VARIABLE;
    private static final ArgumentType TLSV = ArgumentType.VARIABLE;
    private static final ArgumentType S = ArgumentType.STRING;
    private static final ArgumentType T = ArgumentType.TERM;

    public static final AbstractConditionBuilder APPLY_UPDATE_ON_RIGID =
        new ConstructorBasedBuilder(
            "applyUpdateOnRigid", ApplyUpdateOnRigidCondition.class, USV, SV, SV);
    public static final AbstractTacletBuilderCommand NEW_DEPENDING_ON =
        new AbstractTacletBuilderCommand("newDependingOn", SV, SV) {
            @Override
            public void apply(TacletBuilder<?> tb, Object[] arguments, List<String> parameters,
                    boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                tb.addVarsNewDependingOn((org.key_project.logic.op.sv.SchemaVariable) arguments[0],
                    (org.key_project.logic.op.sv.SchemaVariable) arguments[1]);
            }
        };
    public static final AbstractConditionBuilder DROP_EFFECTLESS_ELEMENTARIES =
        new ConstructorBasedBuilder("dropEffectlessElementaries",
            DropEffectlessElementariesCondition.class, USV, SV, SV);
    public static final AbstractConditionBuilder EQUAL_UNIQUE =
        new ConstructorBasedBuilder("equalUnique", EqualUniqueCondition.class, TSV, TSV, FSV);
    public static final AbstractConditionBuilder SIMPLIFY_ITE_UPDATE =
        new ConstructorBasedBuilder("simplifyIfThenElseUpdate",
            SimplifyIfThenElseUpdateCondition.class, FSV, USV, USV, FSV, SV);

    public static final AbstractConditionBuilder STORE_TERM_IN =
        new AbstractConditionBuilder("storeTermIn", SV, T) {
            @Override
            public VariableCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new StoreTermInCondition((SchemaVariable) arguments[0], (Term) arguments[1]);
            }
        };
    public static final AbstractConditionBuilder STORE_EXPR_IN =
        new ConstructorBasedBuilder("storeExprIn", StoreExprInCondition.class, SV, T);
    public static final AbstractConditionBuilder HAS_INVARIANT =
        new ConstructorBasedBuilder("\\hasInvariant", HasLoopInvariantCondition.class, PV, SV);
    public static final AbstractConditionBuilder GET_INVARIANT =
        new ConstructorBasedBuilder("\\getInvariant", LoopInvariantCondition.class, PV, SV, SV);
    public static final AbstractConditionBuilder GET_VARIANT =
        new AbstractConditionBuilder("\\getVariant", PV, SV) {
            @Override
            public VariableCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new LoopVariantCondition((ProgramSV) arguments[0],
                    (SchemaVariable) arguments[1]);
            }
        };

    public static AbstractTacletBuilderCommand NEW_TYPE_OF =
        new AbstractTacletBuilderCommand("newTypeOf", SV, SV) {
            @Override
            public void apply(TacletBuilder<?> tacletBuilder, Object[] arguments,
                    List<String> parameters, boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                tacletBuilder.addVarsNew((org.key_project.logic.op.sv.SchemaVariable) arguments[0],
                    (org.key_project.logic.op.sv.SchemaVariable) arguments[1]);

            }
        };
    public static final AbstractTacletBuilderCommand NEW_RUSTY_TYPE =
        new AbstractTacletBuilderCommand("new", SV, KRT) {
            @Override
            public void apply(TacletBuilder<?> tacletBuilder, Object[] arguments,
                    List<String> parameters, boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                var krt = (KeYRustyType) arguments[1];
                tacletBuilder.addVarsNew((SchemaVariable) arguments[0], krt);
            }
        };

    public static final TacletBuilderCommand NEW_LOCAL_VARS =
        new ConstructorBasedBuilder("newLocalVars", NewLocalVarsCondition.class, SV, SV, SV, SV);

    private static final List<TacletBuilderCommand> tacletBuilderCommands = new ArrayList<>(2);

    static {
        register(APPLY_UPDATE_ON_RIGID, NEW_DEPENDING_ON, EQUAL_UNIQUE,
            DROP_EFFECTLESS_ELEMENTARIES, SIMPLIFY_ITE_UPDATE, NEW_TYPE_OF, NEW_RUSTY_TYPE,
            NEW_LOCAL_VARS, STORE_EXPR_IN, STORE_TERM_IN, HAS_INVARIANT, GET_INVARIANT,
            GET_VARIANT);
    }

    /**
     * Announce a {@link TacletBuilderCommand} for the use during the interpretation of asts. This
     * affects every following interpretation of rule contextes in
     * {@link TacletPBuilder}.
     */
    public static void register(TacletBuilderCommand... cb) {
        for (TacletBuilderCommand a : cb) {
            register(a);
        }
    }

    /**
     * @see #register(TacletBuilderCommand...)
     */
    public static void register(TacletBuilderCommand cb) {
        tacletBuilderCommands.add(cb);
    }


    /**
     * Returns all available {@link TacletBuilderCommand}s that response on the given name.
     *
     * @see TacletBuilderCommand#isSuitableFor(String)
     */
    public static List<TacletBuilderCommand> getConditionBuildersFor(String name) {
        return tacletBuilderCommands.stream().filter(it -> it.isSuitableFor(name))
                .collect(Collectors.toList());
    }
}
