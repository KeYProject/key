/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

import org.jspecify.annotations.NonNull;

/**
 * The default implementation of {@link IExecutionConstraint}.
 *
 * @author Martin Hentschel
 */
public class ExecutionConstraint extends AbstractExecutionElement implements IExecutionConstraint {
    /**
     * The {@link Term} representing the constraint.
     */
    private final @NonNull Term term;

    /**
     * The {@link PosInOccurrence} of the modality of interest.
     */
    private final @NonNull PosInOccurrence modalityPIO;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param term The {@link Term} representing the constraint.
     */
    public ExecutionConstraint(@NonNull ITreeSettings settings, @NonNull Node proofNode,
            @NonNull PosInOccurrence modalityPIO,
            @NonNull Term term) {
        super(settings, proofNode);
        assert term != null;
        assert modalityPIO != null;
        this.term = term;
        this.modalityPIO = modalityPIO;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() throws ProofInputException {
        return formatTerm(term, getServices());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @NonNull String getElementType() {
        return "Constraint";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Term getTerm() {
        return term;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public PosInOccurrence getModalityPIO() {
        return modalityPIO;
    }
}
