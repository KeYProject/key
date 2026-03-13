/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy.breakpoint;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionSideProofUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;

import org.jspecify.annotations.NonNull;


/**
 * This{@link KeYWatchpoint} represents a KeY watchpoint and is responsible to tell the debugger to
 * stop execution when the respective watchpoint evaluates its condition to true.
 *
 * @author Marco Drebing
 */
public class KeYWatchpoint extends AbstractConditionalBreakpoint {
    /**
     * a flag to tell whether the condition should evaluate to true or just be satisfiable
     */
    private boolean suspendOnTrue;

    /**
     * Creates a new {@link AbstractConditionalBreakpoint}. Call setCondition immediately after
     * calling the constructor!
     *
     * @param hitCount the number of hits after which the execution should hold at this breakpoint
     * @param proof the {@link Proof} that will be executed and should stop
     * @param condition the condition as given by the user
     * @param enabled flag if the Breakpoint is enabled
     * @param conditionEnabled flag if the condition is enabled
     * @param containerType the type of the element containing the breakpoint
     * @param suspendOnTrue the flag if the condition needs to evaluate to true or just be
     *        satisfiable
     * @throws SLTranslationException if the condition could not be parsed to a valid Term
     */
    public KeYWatchpoint(int hitCount, Proof proof, String condition, boolean enabled,
            boolean conditionEnabled, KeYJavaType containerType, boolean suspendOnTrue)
            throws SLTranslationException {
        super(hitCount, null, proof, enabled, conditionEnabled, -1, -1, containerType);
        setSuspendOnTrue(suspendOnTrue);
        this.setCondition(condition);
    }

    @Override
    protected StatementBlock getStatementBlock(StatementContainer statementContainer) {
        return (StatementBlock) statementContainer;
    }

    @Override
    protected boolean isInScope(Node node) {
        return true;
    }

    @Override
    protected boolean isInScopeForCondition(Node node) {
        return true;
    }

    @Override
    protected boolean conditionMet(RuleApp ruleApp,
            Node node) {
        if (suspendOnTrue) {
            return super.conditionMet(ruleApp, node);
        } else {
            ApplyStrategyInfo<@NonNull Proof, Goal> info = null;
            try {
                final TermBuilder tb = getProof().getServices().getTermBuilder();
                JTerm negatedCondition = tb.not(getCondition());
                // initialize values
                PosInOccurrence pio = ruleApp.posInOccurrence();
                JTerm term = TermBuilder.goBelowUpdates((JTerm) pio.subTerm());
                IExecutionContext ec =
                    JavaTools.getInnermostExecutionContext(term.javaBlock(),
                        getProof().getServices());
                // put values into map which have to be replaced
                if (ec != null) {
                    getVariableNamingMap().put(getSelfVar(), ec.getRuntimeInstance());
                }
                // replace renamings etc.
                OpReplacer replacer = new OpReplacer(getVariableNamingMap(), tb.tf());
                JTerm termForSideProof = replacer.replace(negatedCondition);
                // start side proof
                JTerm toProof = tb.equals(tb.tt(), termForSideProof);
                // New OneStepSimplifier is required because it has an internal state and the
                // default instance can't be used parallel.
                final ProofEnvironment sideProofEnv = SymbolicExecutionSideProofUtil
                        .cloneProofEnvironmentWithOwnOneStepSimplifier(getProof(), false);
                Sequent sequent =
                    SymbolicExecutionUtil.createSequentToProveWithNewSuccedent(node, pio, toProof);
                info =
                    SymbolicExecutionSideProofUtil.startSideProof(getProof(), sideProofEnv, sequent,
                        StrategyProperties.METHOD_CONTRACT, StrategyProperties.LOOP_INVARIANT,
                        StrategyProperties.QUERY_ON, StrategyProperties.SPLITTING_DELAYED);
                return !info.getProof().closed();
            } catch (ProofInputException e) {
                return false;
            } finally {
                SymbolicExecutionSideProofUtil.disposeOrStore(
                    "KeY Watchpoint evaluation on node " + node.serialNr() + ".", info);
            }
        }
    }

    public boolean isSuspendOnTrue() {
        return suspendOnTrue;
    }

    public void setSuspendOnTrue(boolean suspendOnTrue) {
        this.suspendOnTrue = suspendOnTrue;
    }

    @Override
    public boolean isBreakpointHit(SourceElement activeStatement, RuleApp ruleApp, Node node) {
        if (activeStatement != null && activeStatement.getStartPosition() != Position.UNDEFINED) {
            return super.isBreakpointHit(activeStatement, ruleApp, node);
        }
        return false;
    }
}
