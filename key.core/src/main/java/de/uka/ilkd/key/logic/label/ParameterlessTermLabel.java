/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.rule.LoopScopeInvariantRule;

/**
 * The Class {@link ParameterlessTermLabel} can be used to define labels without parameters.
 *
 * You can use a {@link SingletonLabelFactory} to create a factory for an instance of this class.
 *
 * @see SingletonLabelFactory
 *
 * @author mattias ulbrich
 */
public final class ParameterlessTermLabel implements TermLabel {
    /**
     * Name of {@link #ANON_HEAP_LABEL}.
     */
    public static final Name ANON_HEAP_LABEL_NAME = new Name("anonHeapFunction");

    /**
     * Label attached to anonymisation heap function symbols as for instance introduce in
     * UseOperationContractRule or WhileInvariantRule.
     */
    public static final TermLabel ANON_HEAP_LABEL =
        new ParameterlessTermLabel(ANON_HEAP_LABEL_NAME);

    /**
     * Name of {@link #SELECT_SKOLEM_LABEL}.
     */
    public static final Name SELECT_SKOLEM_LABEL_NAME = new Name("selectSK");

    /**
     * Label attached to skolem constants introduced by the rule pullOutSelect.
     */
    public static final TermLabel SELECT_SKOLEM_LABEL =
        new ParameterlessTermLabel(SELECT_SKOLEM_LABEL_NAME);

    /**
     * Name of {@link #IMPLICIT_SPECIFICATION_LABEL}.
     */
    public static final Name IMPLICIT_SPECIFICATION_LABEL_NAME = new Name("impl");

    /**
     * Label attached to a term which is specified implicitly (by the JML specification).
     */
    public static final TermLabel IMPLICIT_SPECIFICATION_LABEL =
        new ParameterlessTermLabel(IMPLICIT_SPECIFICATION_LABEL_NAME);

    /**
     * Name of {@link #SHORTCUT_EVALUATION_LABEL}.
     */
    public static final Name SHORTCUT_EVALUATION_LABEL_NAME = new Name("SC");

    /**
     * Label attached to a term with the logical operator '{@literal ||}' or '{@literal &&}' to
     * distinguish from '{@literal |}' or '{@literal &}' respectively.
     */
    public static final TermLabel SHORTCUT_EVALUATION_LABEL =
        new ParameterlessTermLabel(SHORTCUT_EVALUATION_LABEL_NAME);

    /**
     * Name of {@link #UNDEFINED_VALUE_LABEL}.
     */
    public static final Name UNDEFINED_VALUE_LABEL_NAME = new Name("undef");

    /**
     * Label attached to a term which denotes an undefined value. At present it is only used for the
     * else-part of the {@link de.uka.ilkd.key.logic.op.IfExThenElse} operator, when it is used for
     * the translation of JML's \min and \max operator. It is necessary to evaluate this constant
     * expression to be not well-defined.
     */
    public static final TermLabel UNDEFINED_VALUE_LABEL =
        new ParameterlessTermLabel(UNDEFINED_VALUE_LABEL_NAME);

    /**
     * Name of {@link #SELF_COMPOSITION_LABEL}.
     */
    public static final Name SELF_COMPOSITION_LABEL_NAME = new Name("selfComposedExecution");

    /**
     * Label attached to the post condition.
     */
    public static final TermLabel SELF_COMPOSITION_LABEL =
        new ParameterlessTermLabel(SELF_COMPOSITION_LABEL_NAME);

    /**
     * Name of {@link #POST_CONDITION_LABEL}.
     */
    public static final Name POST_CONDITION_LABEL_NAME = new Name("postCondition");

    /**
     * Label attached to the post-condition.
     */
    public static final TermLabel POST_CONDITION_LABEL =
        new ParameterlessTermLabel(POST_CONDITION_LABEL_NAME);

    /**
     * Name of {@link #LOOP_SCOPE_INDEX_LABEL}.
     */
    public static final Name LOOP_SCOPE_INDEX_LABEL_NAME = new Name("loopScopeIndex");

    /**
     * Label attached to loop scope index variables in {@link LoopScopeInvariantRule}.
     */
    public static final TermLabel LOOP_SCOPE_INDEX_LABEL =
        new ParameterlessTermLabel(LOOP_SCOPE_INDEX_LABEL_NAME);

    /**
     * The unique name of this label. This is the basename and does not include the parameters
     */
    private final Name name;

    /**
     * Instantiates a new simple term label.
     *
     * @param name the name, not <code>null</code> The fixed associated instantiator, may be
     *        <code>null</code>.
     */
    public ParameterlessTermLabel(Name name) {
        assert name != null;
        this.name = name;
    }

    @Override
    public Name name() {
        return name;
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * Simple term labels have no parameters. This always throws an
     * {@link IndexOutOfBoundsException}.
     */
    @Override
    public Object getChild(int i) {
        throw new IndexOutOfBoundsException();
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * Simple term labels have no parameters. This always returns 0.
     */
    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public String toString() {
        return name.toString();
    }

    /**
     * {@inheritDoc}
     *
     * <p>
     * This object is equal to another {@link ParameterlessTermLabel} iff they bear the same name.
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof ParameterlessTermLabel) {
            ParameterlessTermLabel other = (ParameterlessTermLabel) obj;
            return name.equals(other.name);
        } else {
            return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return name.hashCode();
    }
}
