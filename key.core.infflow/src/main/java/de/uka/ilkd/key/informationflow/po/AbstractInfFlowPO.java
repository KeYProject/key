/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po;

import java.io.IOException;
import java.io.PrintWriter;

import de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.StrategyInfoUndoMethod;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.proof.init.AbstractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.prover.sequent.SequentFormula;

import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo.INF_FLOW_CHECK_TRUE;
import static de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo.PROPERTY_STRATEGY_INF_FLOW_CHECK;


/**
 * Abstract to customize {@link AbstractPO} and {@link AbstractOperationPO}.
 */
public abstract class AbstractInfFlowPO extends AbstractOperationPO implements InfFlowPO {

    protected AbstractInfFlowPO(InitConfig initConfig, String name) {
        super(initConfig, name);
    }

    @Override
    public Proof createProof(String proofName, JTerm poTerm, InitConfig proofConfig) {
        final Proof proof = super.createProof(proofName, poTerm, proofConfig);
        StrategyInfoUndoMethod undo =
            strategyInfos -> strategyInfos.put(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, true);
        proof.openGoals().head().addStrategyInfo(InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY, true,
            undo);

        return proof;
    }

    @Override
    public InfFlowProof createProofObject(String proofName, String proofHeader, JTerm poTerm,
            InitConfig proofConfig) {
        final InfFlowProof proof = new InfFlowProof(proofName, poTerm, proofHeader, proofConfig);

        return proof;
    }

    @Override
    public void prepareSave(StrategyProperties strategyProperties, Proof proof) {
        if (!((InfFlowProof) proof).getIFSymbols().isFreshContract()) {
            strategyProperties.put(PROPERTY_STRATEGY_INF_FLOW_CHECK, INF_FLOW_CHECK_TRUE);
            for (final SequentFormula s : proof.root().sequent().succedent().asList()) {
                ((InfFlowProof) proof).addLabeledTotalTerm((JTerm) s.formula());
            }
        }
    }

    @Override
    public boolean printProofObligation(PrintWriter ps, Proof proof) throws IOException {
        if (proof instanceof InfFlowProof ifProof) {
            if (!(this instanceof InfFlowCompositePO) && ifProof.getIFSymbols().isFreshContract()) {
                return printProofObligation(ps, proof);
            }
        }
        LoggerFactory.getLogger(AbstractInfFlowPO.class)
                .error(
                    "Received a non-information-flow proof for an information proof obligation. Please report.");
        return false;
    }
}
