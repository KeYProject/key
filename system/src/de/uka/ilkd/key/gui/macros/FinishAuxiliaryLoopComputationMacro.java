package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
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
    public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
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
        final LoopInvariant loopInv = loopInvRuleApp.getInvariant();
        final IFProofObligationVars ifVars =
                loopInvRuleApp.getInformationFlowProofObligationVars();


        // create and register resulting taclets
        final Term result = calculateResultingTerm(proof, ifVars, services);
        final Taclet rwTaclet = generateRewriteTaclet(result, loopInv, ifVars, services);
        InfFlowContractPO.addSymbol(rwTaclet, services);
        initiatingGoal.addTaclet(rwTaclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        addContractApplicationTaclets(initiatingGoal, proof);

        saveAuxiliaryProof();

        // close auxiliary computation proof
        mediator.getUI().removeProof(proof);
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