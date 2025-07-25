/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.prover.sequent.PosInOccurrence;

/**
 * The default implementation of {@link IExecutionBranchCondition}.
 *
 * @author Martin Hentschel
 */
public class ExecutionBranchCondition extends AbstractExecutionNode<SourceElement>
        implements IExecutionBranchCondition {
    /**
     * The optional additional branch label.
     */
    private final String additionalBranchLabel;

    /**
     * The {@link JTerm} which represents the branch condition.
     */
    private JTerm branchCondition;

    /**
     * The human readable branch condition.
     */
    private String formatedBranchCondition;

    /**
     * The path condition to reach this node.
     */
    private JTerm pathCondition;

    /**
     * The human readable path condition to reach this node.
     */
    private String formatedPathCondition;

    /**
     * Merged branch conditions.
     */
    private List<Node> mergedProofNodes;

    /**
     * Contains the merged branch conditions.
     */
    private JTerm[] mergedBranchCondtions;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     * @param additionalBranchLabel The optional additional branch label.
     */
    public ExecutionBranchCondition(ITreeSettings settings, Node proofNode,
            String additionalBranchLabel) {
        super(settings, proofNode);
        this.additionalBranchLabel = additionalBranchLabel;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() throws ProofInputException {
        return getFormatedBranchCondition();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getElementType() {
        return "Branch Condition";
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getFormatedBranchCondition() throws ProofInputException {
        if (branchCondition == null) {
            lazyComputeBranchCondition();
        }
        return formatedBranchCondition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isBranchConditionComputed() {
        return branchCondition != null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getBranchCondition() throws ProofInputException {
        if (branchCondition == null) {
            lazyComputeBranchCondition();
        }
        return branchCondition;
    }

    /**
     * Computes the branch condition lazily when {@link #getBranchCondition()} or
     * {@link #getFormatedBranchCondition()} is called the first time.
     *
     * @throws ProofInputException Occurred Exception
     */
    protected void lazyComputeBranchCondition() throws ProofInputException {
        final InitConfig initConfig = getInitConfig();
        if (initConfig != null) { // Otherwise proof is disposed.
            final Services services = initConfig.getServices();
            // Compute branch condition
            if (isMergedBranchCondition()) {
                // Add all merged branch conditions
                JTerm[] mergedConditions = getMergedBranchCondtions();
                branchCondition = services.getTermBuilder().and(mergedBranchCondtions);
                // Simplify merged branch conditions
                if (mergedConditions.length >= 2) {
                    if (getSettings().simplifyConditions()) {
                        branchCondition =
                            SymbolicExecutionUtil.simplify(initConfig, getProof(), branchCondition);
                    }
                    branchCondition =
                        SymbolicExecutionUtil.improveReadability(branchCondition, services);
                }
            } else {
                branchCondition = SymbolicExecutionUtil.computeBranchCondition(getProofNode(),
                    getSettings().simplifyConditions(), true);
            }
            // Format branch condition
            formatedBranchCondition = formatTerm(branchCondition, services);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isPathConditionChanged() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getPathCondition() throws ProofInputException {
        if (pathCondition == null) {
            lazyComputePathCondition();
        }
        return pathCondition;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getFormatedPathCondition() throws ProofInputException {
        if (formatedPathCondition == null) {
            lazyComputePathCondition();
        }
        return formatedPathCondition;
    }

    /**
     * Computes the path condition lazily when {@link #getPathCondition()} or
     * {@link #getFormatedPathCondition()} is called the first time.
     *
     * @throws ProofInputException Occurred Exception
     */
    protected void lazyComputePathCondition() throws ProofInputException {
        InitConfig initConfig = getInitConfig();
        if (initConfig != null) { // Otherwise proof is disposed.
            final Services services = initConfig.getServices();
            // Get path to parent
            JTerm parentPath;
            if (getParent() != null) {
                parentPath = getParent().getPathCondition();
            } else {
                parentPath = services.getTermBuilder().tt();
            }
            // Add current branch condition to path
            JTerm branchCondition = getBranchCondition();
            if (branchCondition == null) {
                return; // Proof disposed in between.
            }
            pathCondition = services.getTermBuilder().and(parentPath, branchCondition);
            // Simplify path condition
            if (getSettings().simplifyConditions()) {
                pathCondition =
                    SymbolicExecutionUtil.simplify(initConfig, getProof(), pathCondition);
            }
            pathCondition = SymbolicExecutionUtil.improveReadability(pathCondition, services);
            // Format path condition
            formatedPathCondition = formatTerm(pathCondition, services);
        }
    }

    /**
     * Adds a merged proof {@link Node}.
     *
     * @param node The proof {@link Node} to add.
     */
    public void addMergedProofNode(Node node) {
        if (mergedProofNodes == null) {
            mergedProofNodes = new LinkedList<>();
            mergedProofNodes.add(getProofNode());
        }
        mergedProofNodes.add(node);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Node[] getMergedProofNodes() {
        return mergedProofNodes != null
                ? mergedProofNodes.toArray(new Node[0])
                : new Node[0];
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm[] getMergedBranchCondtions() throws ProofInputException {
        if (mergedBranchCondtions == null) {
            mergedBranchCondtions = lazyComputeMergedBranchCondtions();
        }
        return mergedBranchCondtions;
    }

    /**
     * Computes the branch condition lazily when {@link #getMergedBranchCondtions()} is called the
     * first time.
     *
     * @throws ProofInputException Occurred Exception
     */
    protected JTerm[] lazyComputeMergedBranchCondtions() throws ProofInputException {
        if (isMergedBranchCondition()) {
            JTerm[] result = new JTerm[mergedProofNodes.size()];
            Iterator<Node> iter = mergedProofNodes.iterator();
            for (int i = 0; i < result.length; i++) {
                result[i] = SymbolicExecutionUtil.computeBranchCondition(iter.next(),
                    getSettings().simplifyConditions(), true);
            }
            return result;
        } else {
            return new JTerm[0];
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isMergedBranchCondition() {
        return mergedProofNodes != null && !mergedProofNodes.isEmpty();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getAdditionalBranchLabel() {
        return additionalBranchLabel;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected IExecutionConstraint[] lazyComputeConstraints() {
        return SymbolicExecutionUtil.createExecutionConstraints(this);
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
    public SourceElement getActiveStatement() {
        JTerm modalityTerm = (JTerm) getModalityPIO().subTerm();
        SourceElement firstStatement = modalityTerm.javaBlock().program().getFirstElement();
        return NodeInfo.computeActiveStatement(firstStatement);
    }
}
