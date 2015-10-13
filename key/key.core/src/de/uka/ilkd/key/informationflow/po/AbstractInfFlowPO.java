/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
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

    public Proof createProof(String proofName,
                             Term poTerm,
                             InitConfig proofConfig) {        
        final Proof proof = super.createProof(proofName, poTerm, proofConfig);
        StrategyInfoUndoMethod undo =
                new StrategyInfoUndoMethod() {
            @Override
            public void undo(
                    de.uka.ilkd.key.util.properties.Properties strategyInfos) {
                strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, true);
            }
        };
        proof.openGoals().head().addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, true, undo);

        return proof;
    }

    public InfFlowProof createProofObject(String proofName,
                                   String proofHeader,
                                   Term poTerm,
                                   InitConfig proofConfig) {
        final InfFlowProof proof = new InfFlowProof(proofName,
                poTerm,
                proofHeader,
                proofConfig);

        return proof;
    }


}