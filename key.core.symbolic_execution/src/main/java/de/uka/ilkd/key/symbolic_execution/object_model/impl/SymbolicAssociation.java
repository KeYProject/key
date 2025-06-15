/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicAssociation;
import de.uka.ilkd.key.symbolic_execution.object_model.ISymbolicObject;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * Default implementation of {@link ISymbolicAssociation}.
 *
 * @author Martin Hentschel
 */
public class SymbolicAssociation extends AbstractElement implements ISymbolicAssociation {
    /**
     * The {@link Services} to use.
     */
    private final Services services;

    /**
     * The array index.
     */
    private final JTerm arrayIndex;

    /**
     * The array start index or {@code null} if not used.
     */
    private final JTerm arrayStartIndex;

    /**
     * The array end index or {@code null} if not used.
     */
    private final JTerm arrayEndIndex;

    /**
     * The {@link IProgramVariable}.
     */
    private final IProgramVariable programVariable;

    /**
     * The target {@link ISymbolicObject}.
     */
    private final ISymbolicObject target;

    /**
     * The optional condition under which this association is valid.
     */
    private final JTerm condition;

    /**
     * Constructor.
     *
     * @param services The {@link Services} to use.
     * @param arrayIndex The array index.
     * @param target The target {@link ISymbolicObject}.
     * @param condition The optional condition under which this association is valid.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicAssociation(Services services, JTerm arrayIndex, ISymbolicObject target,
            JTerm condition, IModelSettings settings) {
        super(settings);
        assert services != null;
        assert target != null;
        this.services = services;
        this.programVariable = null;
        this.arrayIndex = arrayIndex;
        this.target = target;
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
     * @param target The target {@link ISymbolicObject}.
     * @param condition The optional condition under which this association is valid.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicAssociation(Services services, JTerm arrayIndex, JTerm arrayStartIndex,
            JTerm arrayEndIndex, ISymbolicObject target, JTerm condition, IModelSettings settings) {
        super(settings);
        assert services != null;
        assert target != null;
        this.services = services;
        this.programVariable = null;
        this.arrayIndex = arrayIndex;
        this.target = target;
        this.condition = condition;
        this.arrayStartIndex = arrayStartIndex;
        this.arrayEndIndex = arrayEndIndex;
    }

    /**
     * Constructor.
     *
     * @param services The {@link Services} to use.
     * @param programVariable The {@link IProgramVariable}.
     * @param target The target {@link ISymbolicObject}.
     * @param condition The optional condition under which this association is valid.
     * @param settings The {@link IModelSettings} to use.
     */
    public SymbolicAssociation(Services services, IProgramVariable programVariable,
            ISymbolicObject target, JTerm condition, IModelSettings settings) {
        super(settings);
        assert services != null;
        assert programVariable != null;
        assert target != null;
        this.services = services;
        this.programVariable = programVariable;
        this.target = target;
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
    public JTerm getArrayIndex() {
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
    public ISymbolicObject getTarget() {
        return target;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "Association " + getName() + " to " + getTarget();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getCondition() {
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
    public JTerm getArrayStartIndex() {
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
    public JTerm getArrayEndIndex() {
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
