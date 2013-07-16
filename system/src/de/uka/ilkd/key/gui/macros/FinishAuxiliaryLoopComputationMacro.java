package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.LoopInvExecutionPO;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.LoopInvariantBuiltInRuleApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.GuiUtilities;
import de.uka.ilkd.key.util.MiscTools;

public class FinishAuxiliaryLoopComputationMacro extends
        AbstractFinishAuxiliaryComputationMacro {

    private static int i = 0;

    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        final Proof proof = mediator.getSelectedProof();
        final ContractPO poForProof =
                proof.getServices().getSpecificationRepository().getPOForProof(proof);
        return poForProof instanceof LoopInvExecutionPO;
    }

    @Override
    public void applyTo(final KeYMediator mediator,
                        PosInOccurrence posInOcc,
                        ProverTaskListener listener) {
        final Proof proof = mediator.getSelectedProof();
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
        final IFProofObligationVars ifVars = loopInvRuleApp.getInformationFlowProofObligationVars();
        final IFProofObligationVars ifSchemaVars =
                generateApplicationDataSVs(ifVars, proof.getServices());

        // create and register resulting taclets
        final Term result = calculateResultingSVTerm(proof, ifVars, ifSchemaVars, initiatingGoal);
        final Taclet rwTaclet = generateRewriteTaclet(result, loopInv, ifSchemaVars, services);
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

    private Taclet generateRewriteTaclet(Term replacewith,
                                         LoopInvariant loopInv,
                                         IFProofObligationVars ifVars,
                                         Services services) {
        final Name tacletName =
                MiscTools.toValidTacletName("unfold computed formula " + i + " of " +
                                            loopInv.getUniqueName());
        i++;

        // create find term
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(loopInv,
                                                   ifVars.c1, ifVars.c2,
                                                   services);
        final Term find =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);

        //create taclet
        final RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(find);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.ANTECEDENT_POLARITY);
        final RewriteTacletGoalTemplate goal =
                new RewriteTacletGoalTemplate(replacewith);
        tacletBuilder.addTacletGoalTemplate(goal);
        tacletBuilder.addRuleSet(new RuleSet(new Name("concrete")));
        tacletBuilder.setSurviveSmbExec(true);

        return tacletBuilder.getTaclet();
    }
}