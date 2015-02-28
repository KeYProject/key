package de.uka.ilkd.key.informationflow.proof;

import de.uka.ilkd.key.proof.Statistics;

public final class SideProofStatistics extends Statistics {
    private final int sideProofs;

    private SideProofStatistics(int sideProofs,
                                int nodes,
                                int branches,
                                int interactiveSteps,
                                int quantifierInstantiations,
                                int ossApps,
                                int totalRuleApps,
                                int smtSolverApps,
                                int dependencyContractApps,
                                int operationContractApps,
                                int loopInvApps,
                                long autoModeTime) {
        super(nodes, branches, interactiveSteps, quantifierInstantiations, ossApps, totalRuleApps, smtSolverApps, dependencyContractApps, 
                operationContractApps, loopInvApps, autoModeTime, 
                -1, 
                nodes<=sideProofs? .0f: (autoModeTime/(float)(nodes-sideProofs)));
        this.sideProofs = sideProofs;
    }

    static SideProofStatistics create(SideProofStatistics stat) {
        return new SideProofStatistics(1, stat.nodes,
                                       stat.branches,
                                       stat.interactiveSteps,
                                       stat.quantifierInstantiations,
                                       stat.ossApps,
                                       stat.totalRuleApps,
                                       stat.smtSolverApps,
                                       stat.dependencyContractApps,
                                       stat.operationContractApps,
                                       stat.loopInvApps,
                                       stat.autoModeTime);
    }

    static SideProofStatistics create(Statistics stat) {
        return new SideProofStatistics(1, stat.nodes,
                                       stat.branches,
                                       stat.interactiveSteps,
                                       stat.quantifierInstantiations,
                                       stat.ossApps,
                                       stat.totalRuleApps,
                                       stat.smtSolverApps,
                                       stat.dependencyContractApps,
                                       stat.operationContractApps,
                                       stat.loopInvApps,
                                       stat.autoModeTime);
    }

    SideProofStatistics add(SideProofStatistics stat) {
    	return new SideProofStatistics(this.sideProofs + stat.sideProofs,
    	                                   this.nodes + stat.nodes,
                                           this.branches + stat.branches,
                                           this.interactiveSteps + stat.interactiveSteps,
                                           this.quantifierInstantiations + stat.quantifierInstantiations,
                                           this.ossApps + stat.ossApps,
                                           this.totalRuleApps + stat.totalRuleApps,
                                           this.smtSolverApps + stat.smtSolverApps,
                                           this.dependencyContractApps + stat.dependencyContractApps,
                                           this.operationContractApps + stat.operationContractApps,
                                           this.loopInvApps + stat.loopInvApps,
                                           this.autoModeTime + stat.autoModeTime);
    }

    public SideProofStatistics add(Statistics stat) {
    	return new SideProofStatistics(this.sideProofs+1, this.nodes + stat.nodes,
                                           this.branches + stat.branches,
                                           this.interactiveSteps + stat.interactiveSteps,
                                           this.quantifierInstantiations + stat.quantifierInstantiations,
                                           this.ossApps + stat.ossApps,
                                           this.totalRuleApps + stat.totalRuleApps,
                                           this.smtSolverApps + stat.smtSolverApps,
                                           this.dependencyContractApps + stat.dependencyContractApps,
                                           this.operationContractApps + stat.operationContractApps,
                                           this.loopInvApps + stat.loopInvApps,
                                           this.autoModeTime + stat.autoModeTime);
    }

    public SideProofStatistics setAutoModeTime(long autoTime) {
        return new SideProofStatistics(sideProofs, nodes, branches, interactiveSteps,
                        quantifierInstantiations, ossApps, totalRuleApps, smtSolverApps,
                        dependencyContractApps, operationContractApps, loopInvApps, autoTime);
    }
}