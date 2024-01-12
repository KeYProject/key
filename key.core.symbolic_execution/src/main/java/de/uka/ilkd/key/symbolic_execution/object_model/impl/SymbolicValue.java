/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicValue;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicValue}.
 *
 * @author Martin Hentschel
 */
public class SymbolicValue extends AbstractElement implements ISymbolicValue {
    /**
     * The {@link Services} to use.
     */
    private final Services services;

    /**
     * The array index.
     */
    private final Term arrayIndex;

    /**
     * The array start index or {@code null} if not used.
     */
    private final Term arrayStartIndex;

    /**
     * The array end index or {@code null} if not used.
     */
    private final Term arrayEndIndex;

    /**
     * The {@link IProgramVariable}.
     */
    private final IProgramVariable programVariable;

    /**
     * The value {@link Term}.
     */
    private final Term value;

    /**
     * The optional condition under which this value is valid.
     */
    private final Term condition;

    /**
     * Constructor.
     *
     * @param services The {@link Services} to use.
     * @param arrayIndex The array index.
     * @param value The value {@link Term}.
     * @param condition The optional condition under which this value is valid.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicValue(Services services, Term arrayIndex, Term value, Term condition,
            IModelSettings settings) {
        super(settings);
        assert services != null;
        assert arrayIndex != null;
        this.services = services;
        this.programVariable = null;
        this.arrayIndex = arrayIndex;
        this.value = value;
        this.condition = condition;
        this.arrayStartIndex = null;
        this.arrayEndIndex = null;
    }

    /**
     * Constructor.
     *
     * @param services The {@link Services} to use.
     * @param arrayIndex The array index.
     * @param arrayStartIndex The array start index or {@code null} if not used.
     * @param arrayEndIndex The array end index or {@code null} if not used.
     * @param value The value {@link Term}.
     * @param condition The optional condition under which this value is valid.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicValue(Services services, Term arrayIndex, Term arrayStartIndex,
            Term arrayEndIndex, Term value, Term condition, IModelSettings settings) {
        super(settings);
        assert services != null;
        assert arrayIndex != null;
        this.services = services;
        this.programVariable = null;
        this.arrayIndex = arrayIndex;
        this.value = value;
        this.condition = condition;
        this.arrayStartIndex = arrayStartIndex;
        this.arrayEndIndex = arrayEndIndex;
    }

    /**
     * Constructor.
     *
     * @param services The {@link Services} to use.
     * @param programVariable The {@link IProgramVariable}.
     * @param value The value {@link Term}.
     * @param condition The optional condition under which this value is valid.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicValue(Services services, IProgramVariable programVariable, Term value,
            Term condition, IModelSettings settings) {
        super(settings);
        assert services != null;
        assert programVariable != null;
        this.services = services;
        this.programVariable = programVariable;
        this.value = value;
        this.arrayIndex = null;
        this.condition = condition;
        this.arrayStartIndex = null;
        this.arrayEndIndex = null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getName() {
        StringBuilder sb = new StringBuilder();
        if (isArrayRange()) {
            sb.append("[");
            if (getArrayStartIndex() != null) {
                sb.append(getArrayIndexString());
                sb.append(" >= ");
                sb.append(getArrayStartIndexString());
            }
            if (getArrayStartIndex() != null && getArrayEndIndex() != null) {
                sb.append(" and ");
            }
            if (getArrayEndIndex() != null) {
                sb.append(getArrayIndexString());
                sb.append(" <= ");
                sb.append(getArrayEndIndexString());
            }
            sb.append("]");
        } else if (isArrayIndex()) {
            sb.append("[");
            sb.append(getArrayIndexString());
            sb.append("]");
        } else {
            sb.append(getProgramVariableString());
        }
        if (condition != null && condition.op() != Junctor.TRUE) {
            sb.append(" {");
            sb.append(getConditionString());
            sb.append("}");
        }
        return sb.toString();
    }

    /**
     * Checks if an array index is represented.
     *
     * @return {@code true} is array index, {@code false} is something else.
     */
    public boolean isArrayIndex() {
        return arrayIndex != null && (arrayStartIndex == null || arrayEndIndex == null);
    }

    /**
     * Checks if an array range is represented.
     *
     * @return {@code true} is array range, {@code false} is something else.
     */
    public boolean isArrayRange() {
        return arrayStartIndex != null && arrayEndIndex != null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getArrayIndex() {
        return arrayIndex;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IProgramVariable getProgramVariable() {
        return programVariable;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getProgramVariableString() {
        return SymbolicExecutionUtil.getDisplayString(programVariable);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getValue() {
        return value;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getValueString() {
        return formatTerm(value, services);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Sort getType() {
        return value != null ? value.sort() : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getTypeString() {
        Sort sort = getType();
        return sort != null ? sort.toString() : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "Value of " + getName() + " is " + getValueString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getCondition() {
        return condition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getConditionString() {
        return condition != null ? formatTerm(condition, services) : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getArrayIndexString() {
        return arrayIndex != null ? formatTerm(arrayIndex, services) : null;
    }

    /**
     * Returns the array start index.
     *
     * @return The array start index.
     */
    public Term getArrayStartIndex() {
        return arrayStartIndex;
    }

    /**
     * Returns the human readable array start index.
     *
     * @return The human readable array start index.
     */
    public String getArrayStartIndexString() {
        return arrayStartIndex != null ? formatTerm(arrayStartIndex, services) : null;
    }

    /**
     * Returns the array end index.
     *
     * @return The array end index.
     */
    public Term getArrayEndIndex() {
        return arrayEndIndex;
    }

    /**
     * Returns the human readable array end index.
     *
     * @return The human readable array end index.
     */
    public String getArrayEndIndexString() {
        return arrayEndIndex != null ? formatTerm(arrayEndIndex, services) : null;
    }
}
