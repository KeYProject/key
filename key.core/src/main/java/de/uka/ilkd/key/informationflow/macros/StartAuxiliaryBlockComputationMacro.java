/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.informationflow.po.BlockExecutionPO;
import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.informationflow.proof.InfFlowProof;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.BlockContractInternalBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;


/**
 *
 * @author christoph
 */
public class StartAuxiliaryBlockComputationMacro extends AbstractProofMacro
        implements StartSideProofMacro {

    @Override
    public String getName() {
        return "Start auxiliary computation for self-composition proofs";
    }

    @Override
    public String getCategory() {
        return "Information Flow";
    }

    @Override
    public String getDescription() {
        return "In order to increase the efficiency of self-composition "
            + "proofs, this macro starts a side calculation which does "
            + "the symbolic execution only once. The result is "
            + "instantiated twice with the variable to be used in the "
            + "two executions of the self-composition.";
    }

    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            PosInOccurrence posInOcc) {
        if (goals == null || posInOcc == null || goals.isEmpty() || goals.head().node() == null
                || goals.head().node().parent() == null) {
            return false;
        }
        JTerm subTerm = (JTerm) posInOcc.subTerm();

        if (subTerm == null) {
            return false;
        }

        final Services services = proof.getServices();

        final RuleApp app = goals.head().node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractInternalBuiltInRuleApp blockRuleApp)) {
            return false;
        }
        final BlockContract contract = blockRuleApp.getContract();
        final IFProofObligationVars ifVars = blockRuleApp.getInformationFlowProofObligationVars();
        if (ifVars == null) {
            return false;
        }

        final InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(contract, ifVars.c1,
            ifVars.c2, blockRuleApp.getExecutionContext(), services);
        final JTerm selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);

        return RENAMING_TERM_PROPERTY.equalsModThisProperty(subTerm, selfComposedExec);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws Exception {
        final BlockContractInternalBuiltInRuleApp blockRuleApp =
            (BlockContractInternalBuiltInRuleApp) goals.head().node().parent().getAppliedRuleApp();

        final InitConfig initConfig = proof.getEnv().getInitConfigForEnvironment();

        final BlockContract contract = blockRuleApp.getContract();
        final IFProofObligationVars ifVars = blockRuleApp.getInformationFlowProofObligationVars();

        final BlockExecutionPO blockExecPO = new BlockExecutionPO(initConfig, contract,
            ifVars.symbExecVars.labelHeapAtPreAsAnonHeapFunc(), goals.head(),
            blockRuleApp.getExecutionContext(), proof.getServices());

        final InfFlowProof p;
        synchronized (blockExecPO) {
            p = (InfFlowProof) uic.createProof(initConfig, blockExecPO);
        }
        p.unionIFSymbols(((InfFlowProof) proof).getIFSymbols());

        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, p);
        info.addInfo(PROOF_MACRO_FINISHED_INFO_KEY_ORIGINAL_PROOF, proof);
        return info;
    }
}
