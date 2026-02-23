/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.AbstractContractRuleApp;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule.Instantiation;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.FunctionalOperationContractImpl;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionOperationContract;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil.ContractPostOrExcPostExceptionVariableResult;

import org.key_project.util.collection.ImmutableList;

/**
 * The default implementation of {@link IExecutionOperationContract}.
 *
 * @author Martin Hentschel
 */
public class ExecutionOperationContract extends AbstractExecutionNode<SourceElement>
        implements IExecutionOperationContract {
    /**
     * The exception {@link JTerm} used by the applied {@link Contract}.
     */
    private JTerm exceptionTerm;

    /**
     * The result {@link JTerm} used by the applied {@link Contract}.
     */
    private JTerm resultTerm;

    /**
     * The self {@link JTerm} or {@code null} if not available.
     */
    private JTerm selfTerm;

    /**
     * The current contract parameters.
     */
    private ImmutableList<JTerm> contractParams;

    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionOperationContract(ITreeSettings settings, Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected String lazyComputeName() throws ProofInputException {
        if (!isDisposed()) {
            final Services services = getServices();
            // Make sure that the contract is compatible
            if (!(getContract() instanceof FunctionalOperationContract contract)) {
                throw new ProofInputException("Unsupported contract: " + getContract());
            }
            // Compute instantiation
            Instantiation inst = UseOperationContractRule.computeInstantiation(
                (JTerm) getProofNode().getAppliedRuleApp().posInOccurrence().subTerm(), services);
            // Extract used result and exception variable from proof nodes
            resultTerm = searchResultTerm(contract, inst, services);
            ContractPostOrExcPostExceptionVariableResult search =
                SymbolicExecutionUtil.searchContractPostOrExcPostExceptionVariable(
                    getProofNode().child(0), services); // Post branch
            exceptionTerm = search.getExceptionEquality().sub(0);
            // Rename variables in contract to the current one
            List<LocationVariable> heapContext =
                HeapContext.getModifiableHeaps(services, inst.transaction());
            Map<LocationVariable, LocationVariable> atPreVars =
                UseOperationContractRule.computeAtPreVars(heapContext, services, inst);
            Map<LocationVariable, JTerm> atPres = HeapContext.getAtPres(atPreVars, services);
            LocationVariable baseHeap = services.getTypeConverter().getHeapLDT().getHeap();
            JTerm baseHeapTerm = services.getTermBuilder().getBaseHeap();
            if (contract.hasSelfVar()) {
                if (inst.pm().isConstructor()) {
                    selfTerm = searchConstructorSelfDefinition(search.getWorkingTerm(),
                        inst.staticType(), services);
                    if (selfTerm == null) {
                        throw new ProofInputException(
                            "Can't find self term, implementation of UseOperationContractRule might has changed!");
                    }
                    KeYJavaType selfType = services.getJavaInfo().getKeYJavaType(selfTerm.sort());
                    if (inst.staticType() != selfType) {
                        throw new ProofInputException("Type \"" + inst.staticType()
                            + "\" expected but found \"" + selfType
                            + "\", implementation of UseOperationContractRule might has changed!");
                    }
                } else {
                    selfTerm = UseOperationContractRule.computeSelf(baseHeapTerm, atPres, baseHeap,
                        inst, resultTerm, services.getTermFactory());
                }
            }
            contractParams = UseOperationContractRule.computeParams(baseHeapTerm, atPres, baseHeap,
                inst, services.getTermFactory());
            // Compute contract text
            return FunctionalOperationContractImpl.getText(contract, contractParams, resultTerm,
                selfTerm, exceptionTerm, baseHeap, baseHeapTerm, heapContext, atPres, false,
                services, getSettings().usePrettyPrinting(), getSettings().useUnicode()).trim();
        } else {
            return null;
        }
    }

    /**
     * Tries to find the self {@link JTerm} of the given {@link KeYJavaType}.
     *
     * @param term The {@link JTerm} to start search in.
     * @param staticType The expected {@link KeYJavaType}.
     * @param services The {@link Services} to use.
     * @return The found self {@link JTerm} or {@code null} if not available.
     */
    protected JTerm searchConstructorSelfDefinition(JTerm term, KeYJavaType staticType,
            Services services) {
        if (term.op() == Junctor.NOT && term.sub(0).op() == Equality.EQUALS
                && term.sub(0).sub(0).op() instanceof LocationVariable
                && SymbolicExecutionUtil.isNullSort(term.sub(0).sub(1).sort(), services)
                && services.getJavaInfo().getKeYJavaType(term.sub(0).sub(0).sort()) == staticType) {
            return term.sub(0).sub(0);
        } else {
            JTerm result = null;
            int i = term.arity() - 1;
            while (result == null && i >= 0) {
                result = searchConstructorSelfDefinition(term.sub(i), staticType, services);
                i--;
            }
            return result;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getResultTerm() throws ProofInputException {
        synchronized (this) {
            if (!isNameComputed()) {
                getName(); // Compute name and result term
            }
            return resultTerm;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getExceptionTerm() throws ProofInputException {
        synchronized (this) {
            if (!isNameComputed()) {
                getName(); // Compute name and exception term
            }
            return exceptionTerm;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public JTerm getSelfTerm() throws ProofInputException {
        synchronized (this) {
            if (!isNameComputed()) {
                getName(); // Compute name and self term
            }
            return selfTerm;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ImmutableList<JTerm> getContractParams() throws ProofInputException {
        synchronized (this) {
            if (!isNameComputed()) {
                getName(); // Compute name and contract term
            }
            return contractParams;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getFormatedResultTerm() throws ProofInputException {
        JTerm resultTerm = getResultTerm();
        return resultTerm != null ? formatTerm(resultTerm, getServices()) : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getFormatedExceptionTerm() throws ProofInputException {
        JTerm exceptionTerm = getExceptionTerm();
        return exceptionTerm != null ? formatTerm(exceptionTerm, getServices()) : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getFormatedSelfTerm() throws ProofInputException {
        JTerm selfTerm = getSelfTerm();
        return selfTerm != null ? formatTerm(selfTerm, getServices()) : null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getFormatedContractParams() throws ProofInputException {
        ImmutableList<JTerm> contractParams = getContractParams();
        if (contractParams != null && !contractParams.isEmpty()) {
            StringBuilder sb = new StringBuilder();
            boolean afterFirst = false;
            for (JTerm term : contractParams) {
                if (afterFirst) {
                    sb.append(", ");
                } else {
                    afterFirst = true;
                }
                sb.append(formatTerm(term, getServices()));
            }
            return sb.toString();
        } else {
            return null;
        }
    }

    /**
     * Searches the result {@link JTerm}.
     *
     * @param contract The {@link FunctionalOperationContract}.
     * @param inst The {@link Instantiation}.
     * @param services The {@link Services}.
     * @return The found result {@link JTerm} or {@code null} otherwise.
     */
    protected JTerm searchResultTerm(FunctionalOperationContract contract, Instantiation inst,
            Services services) {
        JTerm resultTerm = null;
        if (contract.hasResultVar()) {
            ProgramVariable resultVar =
                extractResultVariableFromPostBranch(getProofNode(), services);
            if (resultVar == null) {
                // Result variable not found in child, create a temporary variable to use in
                // specification
                resultVar = UseOperationContractRule.computeResultVar(inst, services);
            }
            resultTerm = services.getTermBuilder().var(resultVar);
        }
        return resultTerm;
    }

    /**
     * Extracts the result variable from the given post branch.
     *
     * @param node The {@link Node} which is the post or exceptional post branch of an applied
     *        {@link ContractRuleApp}.
     * @param services The {@link Services} to use.
     * @return The found {@link LocationVariable} or {@code null} if not found.
     */
    protected static LocationVariable extractResultVariableFromPostBranch(Node node,
            Services services) {
        JTerm postModality = SymbolicExecutionUtil.posInOccurrenceInOtherNode(node,
            node.getAppliedRuleApp().posInOccurrence(), node.child(0));
        postModality = TermBuilder.goBelowUpdates(postModality);
        MethodFrame mf = JavaTools.getInnermostMethodFrame(postModality.javaBlock(), services);
        SourceElement firstElement = NodeInfo.computeActiveStatement(mf.getFirstElement());
        if (!(firstElement instanceof CopyAssignment assignment)) {
            return null;
        }
        ProgramElement rightChild = assignment.getChildAt(1);
        if (!(rightChild instanceof LocationVariable)) {
            return null;
        }
        return (LocationVariable) rightChild;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Contract getContract() {
        return ((AbstractContractRuleApp) getProofNode().getAppliedRuleApp()).getInstantiation();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IProgramMethod getContractProgramMethod() {
        Contract contract = getContract();
        if (contract instanceof OperationContract) {
            return ((OperationContract) contract).getTarget();
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getElementType() {
        return "Operation Contract";
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
    public boolean isPreconditionComplied() {
        boolean complied = false;
        if (getProofNode().childrenCount() >= 3) {
            complied = getProofNode().child(2).isClosed();
        }
        return complied;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasNotNullCheck() {
        return getProofNode().childrenCount() >= 4;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isNotNullCheckComplied() {
        if (hasNotNullCheck()) {
            return getProofNode().child(3).isClosed();
        } else {
            return false;
        }
    }
}
