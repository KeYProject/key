package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.LoopInvExecutionPO;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.LoopInfFlowUnfoldTacletBuilder;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.GuiUtilities;
import javax.swing.KeyStroke;

public class FinishAuxiliaryLoopComputationMacro extends
        AbstractFinishAuxiliaryComputationMacro {

    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ContractPO poForProof =
                services.getSpecificationRepository().getPOForProof(proof);
        return poForProof instanceof LoopInvExecutionPO;
    }

    @Override
    public void applyTo(final KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) {
        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            return;
        }
        final ContractPO poForProof =
                proof.getServices().getSpecificationRepository().getPOForProof(proof);
        if (!(poForProof instanceof LoopInvExecutionPO)) {
            return;
        }

        final Goal initiatingGoal = ((LoopInvExecutionPO) poForProof).getInitiatingGoal();
        final Services services = initiatingGoal.proof().getServices();

        if (initiatingGoal.node().parent() == null) {
            return;
        }
        final RuleApp app = initiatingGoal.node().parent().getAppliedRuleApp();
        if (!(app instanceof LoopInvariantBuiltInRuleApp)) {
            return;
        }
        final LoopInvariantBuiltInRuleApp loopInvRuleApp =
                (LoopInvariantBuiltInRuleApp)app;
        LoopInvariant loopInv = loopInvRuleApp.retrieveLoopInvariantFromSpecification(services);
        loopInv = loopInv != null ? loopInv : loopInvRuleApp.getInvariant();
        IFProofObligationVars ifVars = loopInvRuleApp.getInformationFlowProofObligationVars();
        ifVars = ifVars.labelHeapAtPreAsAnonHeapFunc();

        // create and register resulting taclets
        final Term result = calculateResultingTerm(proof, ifVars, initiatingGoal);
        final LoopInfFlowUnfoldTacletBuilder tacletBuilder =
                new LoopInfFlowUnfoldTacletBuilder(services);
        tacletBuilder.setLoopInv(loopInv);
        tacletBuilder.setInfFlowVars(ifVars);
        tacletBuilder.setReplacewith(result);
        final Taclet rwTaclet = tacletBuilder.buildTaclet();
        initiatingGoal.proof().addLabeledTotalTerm(result);
        initiatingGoal.proof().addLabeledIFSymbol(rwTaclet);
        initiatingGoal.addTaclet(rwTaclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        addContractApplicationTaclets(initiatingGoal, proof);
        initiatingGoal.proof().unionIFSymbols(proof.getIFSymbols());

        proof.saveProof();

        // close auxiliary computation proof
        GuiUtilities.invokeAndWait(new Runnable() {
            public void run() {
                // make everyone listen to the proof remove
                mediator.startInterface(true);
                mediator.getUI().removeProof(proof);
                // go into automode again
                mediator.stopInterface(true);
            }
        });
    }

    @Override
    public KeyStroke getKeyStroke() {
        return null; // default implementation
    }
}