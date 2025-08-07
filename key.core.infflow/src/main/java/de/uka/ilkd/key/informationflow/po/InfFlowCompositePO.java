/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po;


import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.prover.sequent.SequentFormula;

import static de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo.INF_FLOW_CHECK_PROPERTY;
import static de.uka.ilkd.key.informationflow.proof.InfFlowCheckInfo.INF_FLOW_CHECK_TRUE;

/**
 *
 * @author christoph
 */
public interface InfFlowCompositePO extends InfFlowPO {
    AbstractInfFlowPO getChildPO();

    @Override
    default void prepareSave(StrategyProperties strategyProperties, Proof proof) {
        strategyProperties.put(INF_FLOW_CHECK_PROPERTY, INF_FLOW_CHECK_TRUE);
        for (final SequentFormula s : proof.root().sequent().succedent().asList()) {
            ((InfFlowProof) proof).addLabeledTotalTerm((JTerm) s.formula());
        }
    }
}
