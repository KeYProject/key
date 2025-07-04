/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBaseMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;

/**
 * The default implementation of {@link IExecutionBaseMethodReturn}.
 *
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionMethodReturn<S extends SourceElement>
        extends AbstractExecutionNode<S> implements IExecutionBaseMethodReturn<S> {
    /**
     * The {@link IExecutionMethodCall} which is now returned.
     */
    private final ExecutionMethodCall methodCall;

    /**
     * The signature.
     */
    private String signature;

    /**
     * The method return condition to reach this node from its calling {@link IExecutionMethodCall}.
     */
    private JTerm methodReturnCondition;

    /**
     * The human-readable method return condition to reach this node from its calling
     * {@link IExecutionMethodCall}.
     */
    private String formattedMethodReturnCondition;

    /**
     * The variable value pairs of the state when the method has been called.
     */
    private IExecutionVariable[] callStateVariables;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param methodCall The {@link IExecutionMethodCall} which is now returned.
     */
    protected AbstractExecutionMethodReturn(ITreeSettings settings, Node proofNode,
            ExecutionMethodCall methodCall) {
        super(settings, proofNode);
        assert methodCall != null;
        this.methodCall = methodCall;
        this.methodCall.addMethodReturn(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IExecutionMethodCall getMethodCall() {
        return methodCall;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getSignature() throws ProofInputException {
        if (signature == null) {
            signature = lazyComputeSignature();
        }
        return signature;
    }

    /**
     * Computes the signature lazily when {@link #getSignature()} is called the first time.
     *
     * @return The name including the return value.
     * @throws ProofInputException
     */
    protected abstract String lazyComputeSignature() throws ProofInputException;


    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getMethodReturnCondition() throws ProofInputException {
        if (methodReturnCondition == null) {
            lazyComputeMethodReturnCondition();
        }
        return methodReturnCondition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getFormattedMethodReturnCondition() throws ProofInputException {
        if (methodReturnCondition == null) {
            lazyComputeMethodReturnCondition();
        }
        return formattedMethodReturnCondition;
    }

    /**
     * Computes the method return condition lazily when {@link #getMethodReturnCondition()} or
     * {@link #getFormattedMethodReturnCondition()} is called the first time.
     *
     * @throws ProofInputException Occurred Exception
     */
    protected void lazyComputeMethodReturnCondition() throws ProofInputException {
        final InitConfig initConfig = getProof().getInitConfig();
        if (initConfig != null) { // Otherwise Proof is disposed.
            final Services services = initConfig.getServices();
            // Collect branch conditions
            List<JTerm> bcs = new LinkedList<>();
            AbstractExecutionNode<?> parent = getParent();
            while (parent != null && parent != methodCall) {
                if (parent instanceof IExecutionBranchCondition) {
                    bcs.add(((IExecutionBranchCondition) parent).getBranchCondition());
                }
                parent = parent.getParent();
            }
            // Add current branch condition to path
            methodReturnCondition = services.getTermBuilder().and(bcs);
            // Simplify path condition
            if (getSettings().simplifyConditions()) {
                methodReturnCondition =
                    SymbolicExecutionUtil.simplify(initConfig, getProof(), methodReturnCondition);
            }
            methodReturnCondition =
                SymbolicExecutionUtil.improveReadability(methodReturnCondition, services);
            // Format path condition
            formattedMethodReturnCondition = formatTerm(methodReturnCondition, services);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IExecutionVariable[] getCallStateVariables() throws ProofInputException {
        synchronized (this) {
            if (callStateVariables == null) {
                callStateVariables = lazyComputeCallStateVariables();
            }
            return callStateVariables;
        }
    }

    /**
     * Computes the variables lazily when {@link #getCallStateVariables()} is called the first time.
     *
     * @return The {@link IExecutionVariable}s of the state when the method has been called.
     * @throws ProofInputException
     */
    protected IExecutionVariable[] lazyComputeCallStateVariables() throws ProofInputException {
        // Get relevant information in current node
        Node proofNode = methodCall.getProofNode();
        assert proofNode.childrenCount() == 1;
        PosInOccurrence originalPIO = methodCall.getModalityPIO();
        int index = originalPIO.isInAntec()
                ? proofNode.sequent().antecedent()
                        .indexOf(originalPIO.sequentFormula())
                : proofNode.sequent().succedent()
                        .indexOf(originalPIO.sequentFormula());
        // Search relevant position in child node
        Node childNode = proofNode.child(0);
        SequentFormula nodeSF =
            originalPIO.isInAntec() ? childNode.sequent().antecedent().get(index)
                    : childNode.sequent().succedent().get(index);
        PosInOccurrence modalityPIO =
            new PosInOccurrence(nodeSF, originalPIO.posInTerm(), originalPIO.isInAntec());
        var modalityTerm = modalityPIO.subTerm();
        while (modalityTerm.op() instanceof UpdateApplication) {
            modalityPIO = modalityPIO.down(1);
            modalityTerm = modalityPIO.subTerm();
        }
        // Compute variables
        return SymbolicExecutionUtil.createExecutionVariables(this, childNode, modalityPIO,
            getMethodReturnCondition());
    }
}
