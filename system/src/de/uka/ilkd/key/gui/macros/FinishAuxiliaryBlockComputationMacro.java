/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.BlockExecutionPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.BlockContractBuiltInRuleApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;


/**
 *
 * @author christoph
 */
public class FinishAuxiliaryBlockComputationMacro
        extends AbstractFinishAuxiliaryComputationMacro {

    private static int i = 0;

    @Override
    public boolean canApplyTo(KeYMediator mediator,
                              PosInOccurrence posInOcc) {
        final Proof proof = mediator.getSelectedProof();
        final ContractPO poForProof =
                proof.getServices().getSpecificationRepository().getPOForProof(proof);
        return poForProof instanceof BlockExecutionPO;
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc) {
        final Proof proof = mediator.getSelectedProof();
        final ContractPO poForProof =
                proof.getServices().getSpecificationRepository().getPOForProof(proof);
        if (!(poForProof instanceof BlockExecutionPO)) {
            return;
        }

        final Goal initiatingGoal = ((BlockExecutionPO) poForProof).getInitiatingGoal();
        final Services services = initiatingGoal.proof().getServices();

        if (initiatingGoal.node().parent() == null) {
            return;
        }
        final RuleApp app = initiatingGoal.node().parent().getAppliedRuleApp();
        if (!(app instanceof BlockContractBuiltInRuleApp)) {
            return;
        }
        final BlockContractBuiltInRuleApp blockRuleApp =
                (BlockContractBuiltInRuleApp)app;
        final BlockContract contract = blockRuleApp.getContract();
        final IFProofObligationVars ifVars =
                blockRuleApp.getInformationFlowProofObligationVars();


        // create and register resulting taclets
        final Term result = calculateResultingTerm(proof, ifVars, services);
        if (!InfFlowContractPO.hasSymbols()) {
            InfFlowContractPO.newSymbols(
                    services.getProof().env().getInitConfig().activatedTaclets());
        }
        final Taclet rwTaclet = generateRewriteTaclet(result, contract, ifVars, services);
        InfFlowContractPO.addSymbol(rwTaclet);
        initiatingGoal.addTaclet(rwTaclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        addContractApplicationTaclets(initiatingGoal, proof);

        saveAuxiliaryProof();

        // close auxiliary computation proof
        mediator.getUI().removeProof(proof);
    }


    private Taclet generateRewriteTaclet(Term replacewith,
                                         BlockContract contract,
                                         IFProofObligationVars ifVars,
                                         Services services) {
        final Name tacletName =
                MiscTools.toValidTacletName("unfold computed formula " + i + " of " +
                                            contract.getUniqueName());
        i++;

        // create find term
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(contract,
                                                   ifVars.c1, ifVars.c2,
                                                   services);
        final Term find =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);

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