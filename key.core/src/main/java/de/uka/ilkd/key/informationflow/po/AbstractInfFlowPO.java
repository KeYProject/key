/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.AbstractPO;
import de.uka.ilkd.key.proof.init.InitConfig;


/**
 * Abstract to customize {@link AbstractPO} and {@link AbstractOperationPO}.
 */
public abstract class AbstractInfFlowPO extends AbstractOperationPO implements InfFlowPO {

    public AbstractInfFlowPO(InitConfig initConfig, String name) {
        super(initConfig, name);
    }

    public Proof createProof(String proofName, Term poTerm, InitConfig proofConfig) {
        final Proof proof = super.createProof(proofName, poTerm, proofConfig);
        StrategyInfoUndoMethod undo =
            strategyInfos -> strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, true);
        proof.openGoals().head().addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, true,
            undo);

        return proof;
    }

    public InfFlowProof createProofObject(String proofName, String proofHeader, Term poTerm,
            InitConfig proofConfig) {
        final InfFlowProof proof = new InfFlowProof(proofName, poTerm, proofHeader, proofConfig);

        return proof;
    }


}
