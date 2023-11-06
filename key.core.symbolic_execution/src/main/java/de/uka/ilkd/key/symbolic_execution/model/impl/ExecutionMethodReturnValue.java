/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturnValue;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

/**
 * The default implementation of {@link IExecutionMethodReturnValue}.
 *
 * @author Martin Hentschel
 */
public class ExecutionMethodReturnValue extends AbstractExecutionElement
        implements IExecutionMethodReturnValue {
    /**
     * The return value.
     */
    private final Term returnValue;

    /**
     * The {@link PosInOccurrence} of the modality of interest.
     */
    private final PosInOccurrence modalityPIO;

    /**
     * The return value as human readable {@link String}.
     */
    private String returnValueString;

    /**
     * The optional condition.
     */
    private final Term condition;

    /**
     * The optional condition as human readable {@link String}.
     */
    private String conditionString;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param returnValue The return value.
     * @param condition The optional condition or {@code null} if no condition is available.
     */
    public ExecutionMethodReturnValue(ITreeSettings settings, Node proofNode,
            PosInOccurrence modalityPIO, Term returnValue, Term condition) {
        super(settings, proofNode);
        assert returnValue != null;
        assert modalityPIO != null;
        this.returnValue = returnValue;
        this.condition = condition;
        this.modalityPIO = modalityPIO;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getElementType() {
        return "Return Value";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() throws ProofInputException {
        if (hasCondition()) {
            return getReturnValueString() + " {" + getConditionString() + "}";
        } else {
            return getReturnValueString();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getReturnValue() throws ProofInputException {
        return returnValue;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getReturnValueString() throws ProofInputException {
        if (returnValueString == null) {
            returnValueString = lazyComputeReturnValueString();
        }
        return returnValueString;
    }

    /**
     * Computes the human readable return value of this node lazily when
     * {@link #getReturnValueString()} is called the first time.
     *
     * @return The human readable return value.
     */
    protected String lazyComputeReturnValueString() throws ProofInputException {
        return !isDisposed() ? formatTerm(returnValue, getServices()) : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasCondition() throws ProofInputException {
        return condition != null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getCondition() throws ProofInputException {
        return condition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getConditionString() throws ProofInputException {
        if (conditionString == null) {
            conditionString = lazyComputeConditionString();
        }
        return conditionString;
    }

    /**
     * Computes the human readable return value of this node lazily when
     * {@link #getConditionString()} is called the first time.
     *
     * @return The human readable return value.
     */
    protected String lazyComputeConditionString() throws ProofInputException {
        if (hasCondition()) {
            return !isDisposed() ? formatTerm(condition, getServices()) : null;
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public PosInOccurrence getModalityPIO() {
        return modalityPIO;
    }
}
