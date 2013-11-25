/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
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
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.MethodInfFlowUnfouldTacletBuilder;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.GuiUtilities;
import javax.swing.KeyStroke;


/**
 *
 * @author christoph
 */
public class FinishAuxiliaryComputationMacro
        extends AbstractFinishAuxiliaryComputationMacro {

    private static int i = 0;

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
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
        return poForProof instanceof SymbolicExecutionPO;
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
        if (!(poForProof instanceof SymbolicExecutionPO)) {
            return;
        }
        final Goal initiatingGoal = ((SymbolicExecutionPO) poForProof).getInitiatingGoal();
        final Proof initiatingProof = initiatingGoal.proof();
        final Services services = initiatingProof.getServices();
        final InfFlowContractPO ifPO =
                (InfFlowContractPO) services.getSpecificationRepository()
                                         .getPOForProof(initiatingProof);
        final IFProofObligationVars ifVars = ifPO.getIFVars().labelHeapAtPreAsAnonHeapFunc();
        final InformationFlowContract ifContract = ifPO.getContract();

        // create and register resulting taclets
        final Term result = calculateResultingTerm(proof, ifVars, initiatingGoal);
        final MethodInfFlowUnfouldTacletBuilder tacletBuilder =
                new MethodInfFlowUnfouldTacletBuilder(services);
        tacletBuilder.setContract(ifContract);
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