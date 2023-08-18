/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractBuiltInRuleApp;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionAuxiliaryContract;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionConstraint;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

/**
 * The default implementation of {@link IExecutionAuxiliaryContract}.
 *
 * @author Martin Hentschel
 */
public class ExecutionAuxiliaryContract extends AbstractExecutionNode<SourceElement>
        implements IExecutionAuxiliaryContract {
    /**
     * Constructor.
     *
     * @param settings The {@link ITreeSettings} to use.
     * @param proofNode The {@link Node} of KeY's proof tree which is represented by this
     *        {@link IExecutionNode}.
     */
    public ExecutionAuxiliaryContract(ITreeSettings settings, Node proofNode) {
        super(settings, proofNode);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getElementType() {
        return "Block Contract";
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
    protected String lazyComputeName() throws ProofInputException {
        // Find self term
        Term self = null;
        Term applicationTerm = getModalityPIO().subTerm();
        Term modalityTerm = TermBuilder.goBelowUpdates(applicationTerm);
        ExecutionContext ec =
            JavaTools.getInnermostExecutionContext(modalityTerm.javaBlock(), getServices());
        if (ec != null) {
            ReferencePrefix prefix = ec.getRuntimeInstance();
            if (prefix instanceof ProgramVariable) {
                self = getServices().getTermBuilder().var((ProgramVariable) prefix);
            }
        }
        Node usageNode = getProofNode().child(2);
        assert "Usage".equals(usageNode.getNodeInfo().getBranchLabel())
                : "Block Contract Rule has changed.";
        Term usagePrecondition = usageNode.sequent().antecedent()
                .get(usageNode.sequent().antecedent().size() - 1).formula();
        // Find remembrance heaps and local variables
        while (applicationTerm.op() == UpdateApplication.UPDATE_APPLICATION) {
            assert applicationTerm.sub(0) == usagePrecondition.sub(0)
                    : "Block Contract Rule has changed.";
            applicationTerm = applicationTerm.sub(1);
            usagePrecondition = usagePrecondition.sub(1);
        }
        assert usagePrecondition.op() == UpdateApplication.UPDATE_APPLICATION
                : "Block Contract Rule has changed.";
        Map<LocationVariable, Term> remembranceHeaps = new LinkedHashMap<>();
        Map<LocationVariable, Term> remembranceLocalVariables =
            new LinkedHashMap<>();
        collectRemembranceVariables(usagePrecondition.sub(0), remembranceHeaps,
            remembranceLocalVariables);
        // Find remaining information
        Node validitiyNode = getProofNode().child(0);
        assert "Validity".equals(validitiyNode.getNodeInfo().getBranchLabel())
                : "Block Contract Rule has changed.";
        Term validitiyModalityTerm = TermBuilder.goBelowUpdates(SymbolicExecutionUtil
                .posInOccurrenceInOtherNode(getProofNode(), getModalityPIO(), validitiyNode));
        MethodFrame mf =
            JavaTools.getInnermostMethodFrame(validitiyModalityTerm.javaBlock(), getServices());
        StatementBlock sb = mf != null ? mf.getBody()
                : (StatementBlock) validitiyModalityTerm.javaBlock().program();
        AuxiliaryContract.Variables variables = getContract().getVariables();
        // Skip break and continues
        int statementIndex = variables.breakFlags.size() + variables.continueFlags.size();
        Term returnFlag = null;
        Term result = null;
        if (variables.returnFlag != null) {
            returnFlag = declaredVariableAsTerm(sb, statementIndex);
            statementIndex++; // Skip return flag
            if (variables.result != null) {
                result = declaredVariableAsTerm(sb, statementIndex);
                statementIndex++; // Result variable
            }
        }
        Term exception = null;
        if (variables.exception != null) {
            exception = declaredVariableAsTerm(sb, statementIndex);
        }
        // getPlainText() does not use breakFlags, continueFlags, returnFlag,
        // remembranceLocalVariables, outerRemembrancevariables
        AuxiliaryContract.Terms terms = new AuxiliaryContract.Terms(self, null, null, returnFlag,
            result, exception, remembranceHeaps, remembranceLocalVariables, null, null);

        // Compute text
        return getContract().getPlainText(getServices(), terms);
    }

    /**
     * Returns the variable declared by the statement at the given index as {@link Term}.
     *
     * @param sb The {@link StatementBlock} which contains all variable declarations.
     * @param statementIndex The index in the {@link StatementBlock} with the variable declaration
     *        of interest.
     * @return The variable as {@link Term}.
     */
    protected Term declaredVariableAsTerm(StatementBlock sb, int statementIndex) {
        Statement resultInitStatement = sb.getStatementAt(statementIndex);
        assert resultInitStatement instanceof LocalVariableDeclaration
                : "Block Contract Rule has changed.";
        Named var = ((LocalVariableDeclaration) resultInitStatement).getVariables().get(0)
                .getProgramVariable();
        assert var != null : "Block Contract Rule has changed.";
        return getServices().getTermBuilder().var((ProgramVariable) var);
    }

    /**
     * Collects recursive all remembrance variables.
     *
     * @param term The {@link Term} to start collecting.
     * @param remembranceHeaps The {@link Map} to fill.
     * @param remembranceLocalVariables The {@link Map} to fill.
     */
    protected void collectRemembranceVariables(Term term,
            Map<LocationVariable, Term> remembranceHeaps,
            Map<LocationVariable, Term> remembranceLocalVariables) {
        if (term.op() == UpdateJunctor.PARALLEL_UPDATE) {
            for (Term sub : term.subs()) {
                collectRemembranceVariables(sub, remembranceHeaps, remembranceLocalVariables);
            }
        } else if (term.op() instanceof ElementaryUpdate) {
            ElementaryUpdate eu = (ElementaryUpdate) term.op();
            if (SymbolicExecutionUtil.isHeap(eu.lhs(),
                getServices().getTypeConverter().getHeapLDT())) {
                remembranceHeaps.put((LocationVariable) term.sub(0).op(),
                    getServices().getTermBuilder().var(eu.lhs()));
            } else {
                remembranceLocalVariables.put((LocationVariable) term.sub(0).op(),
                    getServices().getTermBuilder().var(eu.lhs()));
            }
        } else {
            assert false : "Unsupported update term with operator '" + term.op() + "'.";
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isPreconditionComplied() {
        boolean complied = getProofNode().child(1).isClosed();
        return complied;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AuxiliaryContract getContract() {
        return ((AbstractAuxiliaryContractBuiltInRuleApp) getProofNode().getAppliedRuleApp())
                .getContract();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public StatementBlock getBlock() {
        return (StatementBlock) ((AbstractAuxiliaryContractBuiltInRuleApp) getProofNode()
                .getAppliedRuleApp()).getStatement();
    }
}
