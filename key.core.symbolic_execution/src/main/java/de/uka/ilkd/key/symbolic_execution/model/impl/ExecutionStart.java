/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStart;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionTermination;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * The default implementation of {@link IExecutionStart}.
 *
 * @author Martin Hentschel
 */
public class ExecutionStart extends AbstractExecutionNode<SourceElement>
        implements IExecutionStart {
    /**
     * The up to know discovered {@link IExecutionTermination}s.
     */
    private @NonNull ImmutableList<IExecutionTermination> terminations = ImmutableSLList.nil();

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionStart(@NonNull ITreeSettings settings, @NonNull Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected @NonNull String lazyComputeName() {
        return DEFAULT_START_NODE_NAME;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected IExecutionConstraint @NonNull [] lazyComputeConstraints() {
        return SymbolicExecutionUtil.createExecutionConstraints(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @NonNull String getElementType() {
        return "Start";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<IExecutionTermination> getTerminations() {
        return terminations;
    }

    /**
     * Registers the given {@link IExecutionTermination}.
     *
     * @param termination The {@link IExecutionTermination} to register.
     */
    public void addTermination(@Nullable IExecutionTermination termination) {
        if (termination != null) {
            terminations = terminations.append(termination);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected PosInOccurrence lazyComputeModalityPIO() {
        return SymbolicExecutionUtil
                .findModalityWithMaxSymbolicExecutionLabelId(getProofNode().sequent());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable SourceElement getActiveStatement() {
        Term modalityTerm = getModalityPIO().subTerm();
        SourceElement firstStatement = modalityTerm.javaBlock().program().getFirstElement();
        return NodeInfo.computeActiveStatement(firstStatement);
    }

    /**
     * Removes the given termination.
     *
     * @param termination The termination to be deleted.
     * @author Anna Filighera
     */
    public void removeTermination(IExecutionTermination termination) {
        terminations = terminations.removeAll(termination);
    }
}
