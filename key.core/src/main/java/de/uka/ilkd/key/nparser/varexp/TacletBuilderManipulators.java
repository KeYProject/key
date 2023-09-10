/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.varexp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.ServiceLoader;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.conditions.*;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;

import static de.uka.ilkd.key.nparser.varexp.ArgumentType.SORT;
import static de.uka.ilkd.key.nparser.varexp.ArgumentType.TYPE_RESOLVER;
import static de.uka.ilkd.key.rule.conditions.TypeComparisonCondition.Mode.*;

/**
 * This class manages the register of various factories for the different built-in
 * {@link VariableCondition}s.
 *
 * @author Alexander Weigl
 * @version 1 (12/9/19)
 */
public class TacletBuilderManipulators {
    // region Factories
    // Short cut for argument types
    private static final ArgumentType TR = TYPE_RESOLVER;
    private static final ArgumentType KJT = ArgumentType.JAVA_TYPE;
    private static final ArgumentType PV = ArgumentType.VARIABLE;
    private static final ArgumentType USV = ArgumentType.VARIABLE;
    private static final ArgumentType TSV = ArgumentType.VARIABLE;
    private static final ArgumentType ASV = ArgumentType.VARIABLE;
    private static final ArgumentType FSV = ArgumentType.VARIABLE;
    private static final ArgumentType SV = ArgumentType.VARIABLE;
    private static final ArgumentType TLSV = ArgumentType.VARIABLE;
    private static final ArgumentType S = ArgumentType.STRING;
    private static final ArgumentType T = ArgumentType.TERM;


    /**
     *
     */
    public static final AbstractConditionBuilder ABSTRACT_OR_INTERFACE =
        new ConstructorBasedBuilder("isAbstractOrInterface", AbstractOrInterfaceType.class, TR);

    /**
     *
     */
    public static final AbstractConditionBuilder SAME =
        new AbstractConditionBuilder("same", TR, TR) {
            @Override
            public TypeComparisonCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new TypeComparisonCondition((TypeResolver) arguments[0],
                    (TypeResolver) arguments[1],
                    negated ? NOT_SAME : TypeComparisonCondition.Mode.SAME);
            }
        };

    /**
     *
     */
    public static final AbstractConditionBuilder IS_SUBTYPE =
        new AbstractConditionBuilder("sub", TR, TR) {
            @Override
            public TypeComparisonCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new TypeComparisonCondition((TypeResolver) arguments[0],
                    (TypeResolver) arguments[1],
                    negated ? NOT_IS_SUBTYPE : TypeComparisonCondition.Mode.IS_SUBTYPE);
            }
        };

    /**
     *
     */
    public static final AbstractConditionBuilder STRICT =
        new AbstractConditionBuilder("scrictSub", TR, TR) {
            @Override
            public boolean isSuitableFor(@Nonnull String name) {
                if (super.isSuitableFor(name)) {
                    return true;
                }
                return "\\strict\\sub".equalsIgnoreCase(name);
            }

            @Override
            public TypeComparisonCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                return new TypeComparisonCondition((TypeResolver) arguments[0],
                    (TypeResolver) arguments[1], STRICT_SUBTYPE);
            }
        };


    /**
     *
     */
    public static final AbstractConditionBuilder DISJOINT_MODULO_NULL =
        new AbstractConditionBuilder("disjointModuloNull", TR, TR) {
            @Override
            public TypeComparisonCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                return new TypeComparisonCondition((TypeResolver) arguments[0],
                    (TypeResolver) arguments[1], DISJOINTMODULONULL);
            }
        };

    /**
     *
     */
    public static final AbstractTacletBuilderCommand NEW_LABEL =
        new ConstructorBasedBuilder("newLabel", NewJumpLabelCondition.class, SV);

    /**
     *
     */
    public static final AbstractTacletBuilderCommand NEW_JAVATYPE =
        new AbstractTacletBuilderCommand("new", SV, KJT) {
            @Override
            public void apply(TacletBuilder<?> tacletBuilder, Object[] arguments,
                    List<String> parameters, boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                KeYJavaType kjt = (KeYJavaType) arguments[1];
                tacletBuilder.addVarsNew((SchemaVariable) arguments[0], kjt);
            }
        };

    public static final AbstractTacletBuilderCommand NEW_VAR =
        new AbstractTacletBuilderCommand("new", SV, SORT) {
            @Override
            public void apply(TacletBuilder<?> tacletBuilder, Object[] arguments,
                    List<String> parameters, boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                SchemaVariable sv = (SchemaVariable) arguments[0];
                Sort sort = (Sort) arguments[1];
                // TODO weigl tacletBuilder.addVarsNew(sv, sort);
            }
        };


    static class NotFreeInTacletBuilderCommand extends AbstractTacletBuilderCommand {
        public NotFreeInTacletBuilderCommand(@Nonnull ArgumentType... argumentsTypes) {
            super("notFreeIn", argumentsTypes);
        }

        @Override
        public void apply(TacletBuilder<?> tacletBuilder, Object[] arguments,
                List<String> parameters, boolean negated) {
            SchemaVariable x = (SchemaVariable) arguments[0];
            for (int i = 1; i < arguments.length; i++) {
                tacletBuilder.addVarsNotFreeIn(x, (SchemaVariable) arguments[i]);
            }
        }
    }

    public static final AbstractTacletBuilderCommand FREE_1 =
        new NotFreeInTacletBuilderCommand(SV, SV);
    public static final AbstractTacletBuilderCommand FREE_2 =
        new NotFreeInTacletBuilderCommand(SV, SV, SV);
    public static final AbstractTacletBuilderCommand FREE_3 =
        new NotFreeInTacletBuilderCommand(SV, SV, SV, SV);
    public static final AbstractTacletBuilderCommand FREE_4 =
        new NotFreeInTacletBuilderCommand(SV, SV, SV, SV, SV);
    public static final AbstractTacletBuilderCommand FREE_5 =
        new NotFreeInTacletBuilderCommand(SV, SV, SV, SV, SV, SV);

    private static final List<TacletBuilderCommand> tacletBuilderCommands = new ArrayList<>(32);
    public static final AbstractTacletBuilderCommand NEW_TYPE_OF =
        new AbstractTacletBuilderCommand("newTypeOf", SV, SV) {

            @Override
            public void apply(TacletBuilder<?> tacletBuilder, Object[] arguments,
                    List<String> parameters, boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                tacletBuilder.addVarsNew((SchemaVariable) arguments[0],
                    (SchemaVariable) arguments[1]);

            }
        };
    public static final AbstractTacletBuilderCommand NEW_DEPENDING_ON =
        new AbstractTacletBuilderCommand("newDependingOn", SV, SV) {
            @Override
            public void apply(TacletBuilder<?> tb, Object[] arguments, List<String> parameters,
                    boolean negated) {
                if (negated) {
                    throw new IllegalArgumentException("Negation is not supported");
                }
                tb.addVarsNewDependingOn((SchemaVariable) arguments[0],
                    (SchemaVariable) arguments[1]);
            }
        };

    public static final AbstractConditionBuilder FREE_LABEL_IN_VARIABLE =
        new ConstructorBasedBuilder("freeLabelIn", FreeLabelInVariableCondition.class, SV, SV);
    public static final AbstractConditionBuilder DIFFERENT =
        new ConstructorBasedBuilder("different", DifferentInstantiationCondition.class, SV, SV);
    public static final AbstractConditionBuilder FINAL =
        new ConstructorBasedBuilder("final", FinalReferenceCondition.class, SV);
    public static final AbstractConditionBuilder ENUM_CONST =
        new ConstructorBasedBuilder("isEnumConst", EnumConstantCondition.class, SV);
    public static final AbstractConditionBuilder LOCAL_VARIABLE =
        new ConstructorBasedBuilder("isLocalVariable", LocalVariableCondition.class, SV);
    public static final AbstractConditionBuilder ARRAY_LENGTH =
        new ConstructorBasedBuilder("isArrayLength", ArrayLengthCondition.class, SV);
    public static final AbstractConditionBuilder ARRAY =
        new ConstructorBasedBuilder("isArray", ArrayTypeCondition.class, SV);
    public static final AbstractConditionBuilder REFERENCE_ARRAY =
        new AbstractConditionBuilder("isReferenceArray", SV) {
            @Override
            public VariableCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new ArrayComponentTypeCondition((SchemaVariable) arguments[0], !negated);
            }
        };
    public static final AbstractConditionBuilder MAY_EXPAND_METHOD_2 =
        new ConstructorBasedBuilder("mayExpandMethod", MayExpandMethodCondition.class, SV, SV);
    public static final AbstractConditionBuilder MAY_EXPAND_METHOD_3 =
        new ConstructorBasedBuilder("mayExpandMethod", MayExpandMethodCondition.class, SV, SV, SV);
    public static final AbstractConditionBuilder STATIC_METHOD = new ConstructorBasedBuilder(
        "staticMethodReference", StaticMethodCondition.class, SV, SV, SV);
    public static final AbstractConditionBuilder THIS_REFERENCE =
        new ConstructorBasedBuilder("isThisReference", IsThisReference.class, SV);
    public static final AbstractConditionBuilder REFERENCE =
        new AbstractConditionBuilder("isReference", TR) {
            @Override
            public VariableCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                final boolean non_null = parameters.contains("non_null");
                return new TypeCondition((TypeResolver) arguments[0], !negated, non_null);
            }
        };
    public static final AbstractConditionBuilder ENUM_TYPE =
        new ConstructorBasedBuilder("reference", EnumTypeCondition.class, SV, SV, SV);
    public static final AbstractConditionBuilder CONTAINS_ASSIGNMENT =
        new ConstructorBasedBuilder("containsAssignment", ContainsAssignmentCondition.class, SV);
    public static final AbstractConditionBuilder FIELD_TYPE =
        new ConstructorBasedBuilder("fieldType", FieldTypeToSortCondition.class, SV, SORT);
    public static final AbstractConditionBuilder STATIC_REFERENCE =
        new ConstructorBasedBuilder("static", StaticReferenceCondition.class, SV);
    public static final TacletBuilderCommand DIFFERENT_FIELDS =
        new ConstructorBasedBuilder("differentFields", DifferentFields.class, SV, SV);
    public static final AbstractConditionBuilder SAME_OBSERVER =
        new ConstructorBasedBuilder("sameObserver", SameObserverCondition.class, PV, PV);
    public static final AbstractConditionBuilder applyUpdateOnRigid = new ConstructorBasedBuilder(
        "applyUpdateOnRigid", ApplyUpdateOnRigidCondition.class, USV, SV, SV);
    public static final AbstractConditionBuilder DROP_EFFECTLESS_ELEMENTARIES =
        new ConstructorBasedBuilder("dropEffectlessElementaries",
            DropEffectlessElementariesCondition.class, USV, SV, SV);
    public static final AbstractConditionBuilder SIMPLIFY_ITE_UPDATE =
        new ConstructorBasedBuilder("simplifyIfThenElseUpdate",
            SimplifyIfThenElseUpdateCondition.class, FSV, USV, USV, FSV, SV);
    public static final AbstractConditionBuilder SUBFORMULAS =
        new ConstructorBasedBuilder("subFormulas", SubFormulaCondition.class, FSV);
    public static final AbstractConditionBuilder STATIC_FIELD =
        new ConstructorBasedBuilder("isStaticField", StaticFieldCondition.class, FSV);
    public static final AbstractConditionBuilder MODEL_FIELD =
        new ConstructorBasedBuilder("isModelField", ModelFieldCondition.class, FSV);
    public static final AbstractConditionBuilder SUBFORMULA =
        new ConstructorBasedBuilder("hasSubFormulas", SubFormulaCondition.class, FSV);
    public static final TacletBuilderCommand DROP_EFFECTLESS_STORES = new ConstructorBasedBuilder(
        "dropEffectlessStores", DropEffectlessStoresCondition.class, TSV, TSV, TSV, TSV, TSV);
    public static final AbstractConditionBuilder EQUAL_UNIQUE =
        new ConstructorBasedBuilder("equalUnique", EqualUniqueCondition.class, TSV, TSV, FSV);
    public static final AbstractConditionBuilder META_DISJOINT =
        new ConstructorBasedBuilder("metaDisjoint", MetaDisjointCondition.class, TSV, TSV);
    public static final AbstractConditionBuilder IS_OBSERVER =
        new ConstructorBasedBuilder("isObserver", ObserverCondition.class, TSV, TSV);
    public static final AbstractConditionBuilder CONSTANT =
        new ConstructorBasedBuilder("isConstant", ConstantCondition.class, ASV);

    static class JavaTypeToSortConditionBuilder extends AbstractConditionBuilder {
        private final boolean elmen;

        public JavaTypeToSortConditionBuilder(@Nonnull String triggerName, boolean forceElmentary) {
            super(triggerName, SV, SORT);
            this.elmen = forceElmentary;
        }

        @Override
        public VariableCondition build(Object[] arguments, List<String> parameters,
                boolean negated) {
            SchemaVariable v = (SchemaVariable) arguments[0];
            Sort s = (Sort) arguments[1];
            if (!(s instanceof GenericSort)) {
                throw new IllegalArgumentException("Generic sort is expected. Got: " + s);
            } else if (!JavaTypeToSortCondition.checkSortedSV(v)) {
                throw new IllegalArgumentException(
                    "Expected schema variable of kind EXPRESSION or TYPE, but is " + v);
            } else {
                return new JavaTypeToSortCondition(v, (GenericSort) s, this.elmen);
            }
        }
    }

    public static final AbstractConditionBuilder HAS_SORT =
        new JavaTypeToSortConditionBuilder("hasSort", false);
    public static final AbstractConditionBuilder HAS_ELEM_SORT =
        new JavaTypeToSortConditionBuilder("hasElementarySort", true);

    public static final AbstractConditionBuilder LABEL =
        new ConstructorBasedBuilder("hasLabel", TermLabelCondition.class, TSV, S);
    // endregion
    public static final AbstractConditionBuilder STORE_TERM_IN =
        new AbstractConditionBuilder("storeTermIn", SV, T) {
            @Override
            public VariableCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new StoreTermInCondition((SchemaVariable) arguments[0], (Term) arguments[1]);
            }
        };

    public static final AbstractConditionBuilder STORE_STMT_IN =
        new ConstructorBasedBuilder("storeStmtIn", StoreStmtInCondition.class, SV, T);
    public static final AbstractConditionBuilder HAS_INVARIANT =
        new ConstructorBasedBuilder("\\hasInvariant", HasLoopInvariantCondition.class, PV, SV);
    public static final AbstractConditionBuilder GET_INVARIANT =
        new ConstructorBasedBuilder("\\getInvariant", LoopInvariantCondition.class, PV, SV, SV);
    public static final AbstractConditionBuilder GET_FREE_INVARIANT = new ConstructorBasedBuilder(
        "\\getFreeInvariant", LoopFreeInvariantCondition.class, PV, SV, SV);
    public static final AbstractConditionBuilder GET_VARIANT =
        new AbstractConditionBuilder("\\getVariant", PV, SV) {
            @Override
            public VariableCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new LoopVariantCondition((ProgramSV) arguments[0],
                    (SchemaVariable) arguments[1]);
            }
        };
    public static final AbstractConditionBuilder IS_LABELED =
        new AbstractConditionBuilder("isLabeled", PV) {
            @Override
            public IsLabeledCondition build(Object[] arguments, List<String> parameters,
                    boolean negated) {
                return new IsLabeledCondition((ProgramSV) arguments[0], negated);
            }
        };

    public static final AbstractConditionBuilder IS_IN_STRICTFP =
        new ConstructorBasedBuilder("isInStrictFp", InStrictFp.class);

    // region Registry
    static {
        register(SAME_OBSERVER, SIMPLIFY_ITE_UPDATE, ABSTRACT_OR_INTERFACE, SAME, IS_SUBTYPE,
            STRICT, DISJOINT_MODULO_NULL, NEW_JAVATYPE, NEW_VAR, FREE_1, FREE_2, FREE_3, FREE_4,
            FREE_5, NEW_TYPE_OF, NEW_DEPENDING_ON, FREE_LABEL_IN_VARIABLE, DIFFERENT, FINAL,
            ENUM_CONST, LOCAL_VARIABLE, ARRAY_LENGTH, ARRAY, REFERENCE_ARRAY, MAY_EXPAND_METHOD_2,
            MAY_EXPAND_METHOD_3, STATIC_METHOD, THIS_REFERENCE, REFERENCE, ENUM_TYPE,
            CONTAINS_ASSIGNMENT, FIELD_TYPE, STATIC_REFERENCE, DIFFERENT_FIELDS, SAME_OBSERVER,
            applyUpdateOnRigid, DROP_EFFECTLESS_ELEMENTARIES, SIMPLIFY_ITE_UPDATE, SUBFORMULAS,
            STATIC_FIELD, MODEL_FIELD, SUBFORMULA, DROP_EFFECTLESS_STORES, EQUAL_UNIQUE,
            META_DISJOINT,
            IS_OBSERVER, CONSTANT, HAS_SORT, LABEL, NEW_LABEL, HAS_ELEM_SORT, IS_IN_STRICTFP);
        register(STORE_TERM_IN, STORE_STMT_IN, HAS_INVARIANT, GET_INVARIANT, GET_FREE_INVARIANT,
            GET_VARIANT, IS_LABELED);
        loadWithServiceLoader();
    }

    /**
     * Announce a {@link TacletBuilderCommand} for the use during the interpretation of asts. This
     * affects every following interpretation of rule contextes in
     * {@link de.uka.ilkd.key.nparser.builder.TacletPBuilder}.
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
     * Register all {@link TacletBuilderCommand} that are found via the Java's {@link ServiceLoader}
     * facility.
     */
    public static void loadWithServiceLoader() {
        ServiceLoader<TacletBuilderCommand> serviceLoader =
            ServiceLoader.load(TacletBuilderCommand.class);
        serviceLoader.iterator().forEachRemaining(TacletBuilderManipulators::register);
    }

    /**
     * Returns all available {@link TacletBuilderCommand}s.
     */
    public static List<TacletBuilderCommand> getConditionBuilders() {
        return Collections.unmodifiableList(tacletBuilderCommands);
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
    // endregion
}
