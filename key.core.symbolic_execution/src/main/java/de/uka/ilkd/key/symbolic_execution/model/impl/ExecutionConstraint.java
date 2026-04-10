/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

import org.key_project.prover.sequent.PosInOccurrence;

/**
 * The default implementation of {@link IExecutionConstraint}.
 *
 * @author Martin Hentschel
 */
public class ExecutionConstraint extends AbstractExecutionElement implements IExecutionConstraint {
    /**
     * The {@link JTerm} representing the constraint.
     */
    private final JTerm term;

    /**
     * The {@link PosInOccurrence} of the modality of interest.
     */
    private final PosInOccurrence modalityPIO;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param term The {@link JTerm} representing the constraint.
     */
    public ExecutionConstraint(ITreeSettings settings, Node proofNode,
            PosInOccurrence modalityPIO,
            JTerm term) {
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
    public String getElementType() {
        return "Constraint";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getTerm() {
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
