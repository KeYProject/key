/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule;

import de.uka.ilkd.key.informationflow.po.SymbolicExecutionPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.LoopContractInternalRule;
import de.uka.ilkd.key.speclang.LoopContract;

/**
 *
 * @author Alexander Weigl
 * @version 1 (8/7/25)
 */
public class InfFlowLoopContractInternalRule extends LoopContractInternalRule {
    @Override
    protected boolean contractApplied(LoopContract contract, Goal goal) {
        if (!super.contractApplied(contract, goal)) {
            Services services = goal.proof().getServices();
            Proof proof = goal.proof();
            ProofOblInput po = services.getSpecificationRepository().getProofOblInput(proof);
            if (po instanceof SymbolicExecutionPO) {
                Goal initiatingGoal = ((SymbolicExecutionPO) po).getInitiatingGoal();
                return contractApplied(contract, initiatingGoal);
            }
        }
        return false;
    }
}
