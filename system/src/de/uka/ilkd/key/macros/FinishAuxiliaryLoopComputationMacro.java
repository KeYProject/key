package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.ProverTaskListener;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.LoopInvExecutionPO;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.LoopInfFlowUnfoldTacletBuilder;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.ui.UserInterface;
import de.uka.ilkd.key.util.ThreadUtilities;

public class FinishAuxiliaryLoopComputationMacro extends
        AbstractFinishAuxiliaryComputationMacro {

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              ImmutableList<Goal> goals,
                              PosInOccurrence posInOcc) {
        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
                services.getSpecificationRepository().getProofOblInput(proof);
        return poForProof instanceof LoopInvExecutionPO;
    }

    @Override
    public ProofMacroFinishedInfo applyTo(final KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          ProverTaskListener listener) {
        final Proof proof = mediator.getSelectedProof();
        if (proof == null) {
            return null;
        }

        final ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals, proof);
        final ProofOblInput poForProof =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
        if (!(poForProof instanceof LoopInvExecutionPO)) {
            return info;
        }
        final LoopInvExecutionPO loopInvExecPO = (LoopInvExecutionPO) poForProof;

        final Goal initiatingGoal = loopInvExecPO.getInitiatingGoal();
        final Proof initiatingProof = initiatingGoal.proof();
        final Services services = initiatingProof.getServices();

        if (initiatingGoal.node().parent() == null) {
            return info;
        }
        final RuleApp app = initiatingGoal.node().parent().getAppliedRuleApp();
        if (!(app instanceof LoopInvariantBuiltInRuleApp)) {
            return info;
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
        tacletBuilder.setExecutionContext(loopInvRuleApp.getExecutionContext());
        tacletBuilder.setInfFlowVars(ifVars);
        tacletBuilder.setReplacewith(result);
        tacletBuilder.setGuard(loopInvExecPO.getGuard());
        final Taclet rwTaclet = tacletBuilder.buildTaclet();
        initiatingGoal.proof().addLabeledTotalTerm(result);
        initiatingGoal.proof().addLabeledIFSymbol(rwTaclet);
        initiatingGoal.addTaclet(rwTaclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        addContractApplicationTaclets(initiatingGoal, proof);
        initiatingGoal.proof().unionIFSymbols(proof.getIFSymbols());
        initiatingGoal.proof().getIFSymbols().useProofSymbols();

        // close auxiliary computation proof
        ThreadUtilities.invokeAndWait(new Runnable() {
            public void run() {
                final UserInterface ui = mediator.getUI();
                if (ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().autoSave()
                        && !proof.name().toString().endsWith(".proof")) {
                    assert ui.getMediator().getSelectedProof().name().equals(proof.name());
                    ui.saveProof(proof, ".proof");
                }
                // make everyone listen to the proof remove
                mediator.startInterface(true);
                initiatingProof.addSideProof(proof);
                mediator.getUI().removeProof(proof);
                mediator.getSelectionModel().setSelectedGoal(initiatingGoal);
                // go into automode again
                mediator.stopInterface(true);
            }
        });
        return new ProofMacroFinishedInfo(this, initiatingGoal);
    }
}