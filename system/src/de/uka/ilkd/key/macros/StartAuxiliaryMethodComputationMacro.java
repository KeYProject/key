/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.ui.UserInterface;

/**
 *
 * @author christoph
 */
public class StartAuxiliaryMethodComputationMacro extends AbstractProofMacro {

    @Override
    public String getName() {
        return "Start auxiliary computation for self-composition proofs";
    }

    @Override
    public String getDescription() {
        return "In order to increase the efficiency of self-composition " +
               "proofs, this macro starts a side calculation which does " +
               "the symbolic execution only once. The result is " +
               "instantiated twice with the variable to be used in the " +
               "two executions of the self-composition.";
    }

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        if (goals == null || goals.head() == null) {
            return false;
        }
        if (posInOcc == null
                || posInOcc.subTerm() == null) {
            return false;
        }
        Proof proof = goals.head().proof();
        Services services = proof.getServices();
        ProofOblInput poForProof =
                services.getSpecificationRepository().getProofOblInput(proof);
        if (!(poForProof instanceof InfFlowContractPO)) {
            return false;
        }
        final InfFlowContractPO po = (InfFlowContractPO) poForProof;

        final InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(po.getContract(),
                                                   po.getIFVars().c1,
                                                   po.getIFVars().c2, services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);

        return posInOcc.subTerm().equalsModRenaming(selfComposedExec);
    }

    @Override
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        final Proof proof = goals.head().proof();

        final Services services = proof.getServices();
        final ProofOblInput poForProof = services.getSpecificationRepository().getProofOblInput(proof);
        if (!(poForProof instanceof InfFlowContractPO)) {
            return info;
        }

        final InitConfig initConfig = proof.getEnv().getInitConfigForEnvironment();
        final InfFlowContractPO po = (InfFlowContractPO) poForProof;

        final SymbolicExecutionPO symbExecPO =
                new SymbolicExecutionPO(initConfig, po.getContract(),
                                        po.getIFVars().symbExecVars.labelHeapAtPreAsAnonHeapFunc(),
                                        goals.head(), proof.getServices());
        final UserInterface ui = mediator.getUI();
        try {
            final Proof p;
            synchronized (symbExecPO) {
                p = ui.createProof(initConfig, symbExecPO);
            }
            p.unionIFSymbols(proof.getIFSymbols());
            // stop interface again, because it is activated by the proof
            // change through startProver; the ProofMacroWorker will activate
            // it again at the right time
            mediator.stopInterface(true);
            mediator.setInteractive(false);
            info = new ProofMacroFinishedInfo(this, p);
        } catch (ProofInputException exc) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), exc);
        }
        return info;
    }
}