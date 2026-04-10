/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.proof;

import de.uka.ilkd.key.proof.Statistics;

/**
 * Statistics for additional side proofs as, e.g., performed by information flow macro
 *
 * @author Michael Kirsten
 */
public final class SideProofStatistics extends Statistics {

    /**
     * Keep track of the amount of side proofs (can also be nested)
     */
    private final int sideProofs;

    /**
     * Construct new side proof statistics
     *
     * @param sideProofs the amount of side proofs
     * @param nodes amount of nodes
     * @param branches amount of branches
     * @param interactiveSteps amount of interactive steps
     * @param symbExApps amount of symbolic execution steps
     * @param quantifierInstantiations amount of quantifier instantiations
     * @param ossApps amount of one-step-simplifier applications
     * @param mergeRuleApps amount of merge rule applications
     * @param totalRuleApps amount of total rule applications
     * @param smtSolverApps amount of SMT solver calls
     * @param dependencyContractApps amount of dependency contract applications
     * @param operationContractApps amount of operation contract applications
     * @param blockLoopContractApps amount of block or loop contract applications
     * @param loopInvApps amount of loop invariant rule applications
     * @param autoModeTime accumulated (spent) auto mode time
     */
    private SideProofStatistics(int sideProofs, int nodes, int branches, int interactiveSteps,
            int symbExApps, int quantifierInstantiations, int ossApps, int mergeRuleApps,
            int totalRuleApps, int smtSolverApps, int dependencyContractApps,
            int operationContractApps, int blockLoopContractApps, int loopInvApps,
            long autoModeTime) {
        super(nodes, branches, 0, interactiveSteps, symbExApps, quantifierInstantiations, ossApps,
            mergeRuleApps, totalRuleApps, smtSolverApps, dependencyContractApps,
            operationContractApps, blockLoopContractApps, loopInvApps, autoModeTime, -1,
            nodes <= sideProofs ? .0f : (autoModeTime / (float) (nodes - sideProofs)));
        this.sideProofs = sideProofs;
    }

    /**
     * Create a new side proof statistics object from existing side proof statistics.
     *
     * @param stat side proof statistics object.
     * @return a new identical side proof statistics object, but with the side proof number set to
     *         one.
     */
    static SideProofStatistics create(SideProofStatistics stat) {
        return new SideProofStatistics(1, stat.nodes, stat.branches, stat.interactiveSteps,
            stat.symbExApps, stat.quantifierInstantiations, stat.ossApps, stat.mergeRuleApps,
            stat.totalRuleApps, stat.smtSolverApps, stat.dependencyContractApps,
            stat.operationContractApps, stat.blockLoopContractApps, stat.loopInvApps,
            stat.autoModeTimeInMillis);
    }

    /**
     * Create a new side proof statistics object from existing proof statistics.
     *
     * @param stat proof statistics object.
     * @return a new identical side proof statistics object, but as side proof statistics and with
     *         the side proof number set to one.
     */
    static SideProofStatistics create(Statistics stat) {
        return new SideProofStatistics(1, stat.nodes, stat.branches, stat.interactiveSteps,
            stat.symbExApps, stat.quantifierInstantiations, stat.ossApps, stat.mergeRuleApps,
            stat.totalRuleApps, stat.smtSolverApps, stat.dependencyContractApps,
            stat.operationContractApps, stat.blockLoopContractApps, stat.loopInvApps,
            stat.autoModeTimeInMillis);
    }

    /**
     * Add side proof statistics to current one.
     *
     * @param stat another side proof statistics object.
     * @return the sum of both side proof statistics objects.
     */
    SideProofStatistics add(SideProofStatistics stat) {
        return new SideProofStatistics(this.sideProofs + stat.sideProofs, this.nodes + stat.nodes,
            this.branches + stat.branches, this.interactiveSteps + stat.interactiveSteps,
            this.symbExApps + stat.symbExApps,
            this.quantifierInstantiations + stat.quantifierInstantiations,
            this.ossApps + stat.ossApps, this.mergeRuleApps + stat.mergeRuleApps,
            this.totalRuleApps + stat.totalRuleApps, this.smtSolverApps + stat.smtSolverApps,
            this.dependencyContractApps + stat.dependencyContractApps,
            this.operationContractApps + stat.operationContractApps,
            this.blockLoopContractApps + stat.blockLoopContractApps,
            this.loopInvApps + stat.loopInvApps,
            this.autoModeTimeInMillis + stat.autoModeTimeInMillis);
    }

    /**
     * Add proof statistics to current side proof statistics object.
     *
     * @param stat a proof statistics object.
     * @return the sum of the proof statistics and the side proof statistics object.
     */
    public SideProofStatistics add(Statistics stat) {
        return new SideProofStatistics(this.sideProofs + 1, this.nodes + stat.nodes,
            this.branches + stat.branches, this.interactiveSteps + stat.interactiveSteps,
            this.symbExApps + stat.symbExApps,
            this.quantifierInstantiations + stat.quantifierInstantiations,
            this.ossApps + stat.ossApps, this.mergeRuleApps + stat.mergeRuleApps,
            this.totalRuleApps + stat.totalRuleApps, this.smtSolverApps + stat.smtSolverApps,
            this.dependencyContractApps + stat.dependencyContractApps,
            this.operationContractApps + stat.operationContractApps,
            this.blockLoopContractApps + stat.blockLoopContractApps,
            this.loopInvApps + stat.loopInvApps,
            this.autoModeTimeInMillis + stat.autoModeTimeInMillis);
    }

    /**
     * Set time spent in auto mode.
     *
     * @param autoTime auto mode time as long data type.
     * @return identical side proof statistics object, but with changed auto mode time.
     */
    public SideProofStatistics setAutoModeTime(long autoTime) {
        return new SideProofStatistics(sideProofs, nodes, branches, interactiveSteps, symbExApps,
            quantifierInstantiations, ossApps, mergeRuleApps, totalRuleApps, smtSolverApps,
            dependencyContractApps, operationContractApps, blockLoopContractApps, loopInvApps,
            autoTime);
    }
}
