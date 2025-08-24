/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key;

import java.util.List;

import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.informationflow.proof.SideProofStatistics;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;

import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (8/3/25)
 */
@NullMarked
public class InfFlowStatistics extends Statistics {
    private boolean sideProofs;
    private Statistics stat;

    protected InfFlowStatistics(int nodes, int branches, int cachedBranches, int interactiveSteps,
            int symbExApps, int quantifierInstantiations, int ossApps, int mergeRuleApps,
            int totalRuleApps, int smtSolverApps, int dependencyContractApps,
            int operationContractApps, int blockLoopContractApps, int loopInvApps,
            long autoModeTimeInMillis, long timeInMillis, float timePerStepInMillis) {
        super(nodes, branches, cachedBranches, interactiveSteps, symbExApps,
            quantifierInstantiations, ossApps, mergeRuleApps, totalRuleApps, smtSolverApps,
            dependencyContractApps, operationContractApps, blockLoopContractApps, loopInvApps,
            autoModeTimeInMillis, timeInMillis, timePerStepInMillis);
    }

    public InfFlowStatistics(List<Node> startNodes) {
        super(startNodes);
    }

    @Override
    protected void generateSummary(Proof proof) {
        super.generateSummary(proof);
        if (proof instanceof InfFlowProof ifp) { // TODO: get rid of that instanceof by subclassing
            generateSummary(ifp);
        }
    }

    protected void generateSummary(InfFlowProof proof) {
        sideProofs = proof.hasSideProofs();
        if (sideProofs) {
            final long autoTime = proof.getAutoModeTime()
                    + proof.getSideProofStatistics().autoModeTimeInMillis;
            final SideProofStatistics side = proof.getSideProofStatistics()
                    .add(this).setAutoModeTime(autoTime);
            stat = create(side, proof.getCreationTime());
        }
    }
}
