/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import java.util.Objects;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.ContractRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

public class MethodBreakpoint extends AbstractConditionalBreakpoint {
    /**
     * flag to tell whether to stop on method entry
     */
    private boolean isEntry;

    /**
     * flag to tell whether to stop on method exit
     */
    private boolean isExit;

    /**
     * The start of the method containing the associated Breakpoint
     */
    protected final int methodStart;

    /**
     * The end of the method containing the associated Breakpoint
     */
    protected final int methodEnd;

    /**
     * The path of the class this {@link LineBreakpoint} is associated with.
     */
    private String classPath;

    /**
     * Creates a new {@link LineBreakpoint}.
     *
     * @param classPath the path of the class the associated Breakpoint lies within
     * @param lineNumber the line where the associated Breakpoint is located in the class
     * @param hitCount the number of hits after which the execution should hold at this breakpoint
     * @param pm the {@link IProgramMethod} representing the Method which the Breakpoint is located
     *        at
     * @param proof the {@link Proof} that will be executed and should stop
     * @param condition the condition as given by the user
     * @param enabled flag if the Breakpoint is enabled
     * @param conditionEnabled flag if the condition is enabled
     * @param methodStart the line the containing method of this breakpoint starts at
     * @param methodEnd the line the containing method of this breakpoint ends at
     * @param isEntry flag to tell whether to stop on method entry
     * @param isExit flag to tell whether to stop on method exit
     * @throws SLTranslationException if the condition could not be parsed to a valid Term
     */
    public MethodBreakpoint(String classPath, int lineNumber, int hitCount, IProgramMethod pm,
            Proof proof, String condition, boolean enabled, boolean conditionEnabled,
            int methodStart, int methodEnd, boolean isEntry, boolean isExit)
            throws SLTranslationException {
        super(hitCount, pm, proof, enabled, conditionEnabled, methodStart, methodEnd,
            pm.getContainerType());
        this.isEntry = isEntry;
        this.isExit = isExit;
        this.setClassPath(classPath);
        this.methodEnd = methodEnd;
        this.methodStart = methodStart;
        this.setCondition(condition);
    }

    @Override
    public boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Proof proof,
            Node node) {
        return !proof.isDisposed()
                && ((isEntry && isMethodCallNode(node, ruleApp))
                        || (isExit && isMethodReturnNode(node, ruleApp)))
                && (!isConditionEnabled() || conditionMet(ruleApp, proof, node)) && isEnabled()
                && hitcountExceeded(node);
    }

    /**
     * @param node to check
     * @param ruleApp the applied rule app
     * @return true if the node represents a method call
     */
    private boolean isMethodCallNode(Node node, RuleApp ruleApp) {
        SourceElement statement = NodeInfo.computeActiveStatement(ruleApp);
        IProgramMethod currentPm = null;
        if (statement instanceof MethodBodyStatement mbs) {
            currentPm = mbs.getProgramMethod(getProof().getServices());
        }
        if (currentPm != null && currentPm.equals(getPm())
                && SymbolicExecutionUtil.isMethodCallNode(node, ruleApp, statement)) {
            return true;
        } else if (ruleApp instanceof ContractRuleApp methodRuleApp) {
            Contract contract = methodRuleApp.getInstantiation();
            if (contract instanceof FunctionalOperationContract methodContract) {
                return methodContract.getTarget().equals(getPm());
            }
        }
        return false;
    }

    /**
     * @param node to check
     * @param ruleApp the applied rule app
     * @return true if the node represents a method return
     */
    private boolean isMethodReturnNode(Node node, RuleApp ruleApp) {
        if ((SymbolicExecutionUtil.isMethodReturnNode(node, ruleApp)
                || SymbolicExecutionUtil.isExceptionalMethodReturnNode(node, ruleApp))
                && isCorrectMethodReturn(node, ruleApp)) {
            return true;
        } else if (ruleApp instanceof ContractRuleApp methodRuleApp) {
            Contract contract = methodRuleApp.getInstantiation();
            if (contract instanceof FunctionalOperationContract methodContract) {
                return methodContract.getTarget().equals(getPm());
            }
        }
        return false;
    }

    private boolean isCorrectMethodReturn(Node node, RuleApp ruleApp) {
        Term term = ruleApp.posInOccurrence().subTerm();
        term = TermBuilder.goBelowUpdates(term);
        MethodFrame mf =
            JavaTools.getInnermostMethodFrame(term.javaBlock(), node.proof().getServices());
        return Objects.equals(getPm(), mf.getProgramMethod());
    }

    @Override
    protected StatementBlock getStatementBlock(StatementContainer statementContainer) {
        return (StatementBlock) statementContainer;
    }

    public boolean isEntry() {
        return isEntry;
    }

    public void setEntry(boolean isEntry) {
        this.isEntry = isEntry;
    }

    public boolean isExit() {
        return isExit;
    }

    public void setExit(boolean isExit) {
        this.isExit = isExit;
    }

    @Override
    protected boolean isInScope(Node node) {
        Node checkNode = node;
        while (checkNode != null) {
            SourceElement activeStatement =
                NodeInfo.computeActiveStatement(checkNode.getAppliedRuleApp());
            if (activeStatement != null
                    && activeStatement.getStartPosition() != Position.UNDEFINED) {
                if (activeStatement.getStartPosition().line() >= methodStart
                        && activeStatement.getEndPosition().line() <= methodEnd) {
                    return true;
                }
                break;
            }
            checkNode = checkNode.parent();
        }
        return false;
    }

    @Override
    protected boolean isInScopeForCondition(Node node) {
        Node checkNode = node;
        while (checkNode != null) {
            SourceElement activeStatement =
                NodeInfo.computeActiveStatement(checkNode.getAppliedRuleApp());
            if (activeStatement != null
                    && activeStatement.getStartPosition() != Position.UNDEFINED) {
                if (activeStatement.getStartPosition().line() >= methodStart
                        && activeStatement.getEndPosition().line() <= methodEnd
                        && activeStatement instanceof LocalVariableDeclaration) {
                    return true;
                }
                break;
            }
            checkNode = checkNode.parent();
        }
        return false;
    }

    /**
     * @return the classPath
     */
    public String getClassPath() {
        return classPath;
    }

    /**
     * @param classPath the classPath to set
     */
    public void setClassPath(String classPath) {
        this.classPath = classPath;
    }
}
