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
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.InfFlowProofSymbols;
import de.uka.ilkd.key.proof.init.SymbolicExecutionPO;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.util.MiscTools;


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
        Proof proof = mediator.getSelectedProof();
        Services services = proof.getServices();
        ContractPO poForProof =
                services.getSpecificationRepository().getPOForProof(proof);
        return poForProof instanceof SymbolicExecutionPO;
    }


    @Override
    public void applyTo(KeYMediator mediator,
                        PosInOccurrence posInOcc) {
        Proof proof = mediator.getSelectedProof();
        ContractPO poForProof =
                proof.getServices().getSpecificationRepository().getPOForProof(proof);
        if (!(poForProof instanceof SymbolicExecutionPO)) {
            return;
        }
        SymbolicExecutionPO po = (SymbolicExecutionPO) poForProof;
        Goal initiatingGoal = po.getInitiatingGoal();
        Proof initiatingProof = initiatingGoal.proof();
        Services services = initiatingProof.getServices();
        SpecificationRepository specRepos = services.getSpecificationRepository();
        InfFlowContractPO ifPO = (InfFlowContractPO) specRepos.getPOForProof(initiatingProof);
        InfFlowProofSymbols s = specRepos.getInfFlowProofSymbols(ifPO.getContract().getTarget());

        // create and register resulting taclets
        Term result = calculateResultingTerm(proof, ifPO.getIFVars(), services);
        Taclet rwTaclet = generateRewriteTaclet(result, ifPO, services);
        s.addTaclet(rwTaclet, services);
        s.addTerms(ifPO.getIFVars().c1.termList.append(ifPO.getIFVars().c2.termList
                .append(ifPO.getIFVars().symbExecVars.termList)));
        s.addTerm(result);
        initiatingGoal.addTaclet(rwTaclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
        addContractApplicationTaclets(initiatingGoal, proof);

        saveAuxiliaryProof();

        // close auxiliary computation proof
        mediator.getUI().removeProof(proof);
    }


    private Taclet generateRewriteTaclet(Term replacewith,
                                         InfFlowContractPO infPO,
                                         Services services) {
        Name tacletName =
                MiscTools.toValidTacletName("unfold computed formula " + i + " of " +
                                            infPO.getContract().getTarget().getFullName());
        i++;

        // create find term
        IFProofObligationVars ifVars = infPO.getIFVars();
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(infPO.getContract(),
                                                   ifVars.c1, ifVars.c2,
                                                   services);
        Term find =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);

        //create taclet
        RewriteTacletBuilder tacletBuilder = new RewriteTacletBuilder();
        tacletBuilder.setName(tacletName);
        tacletBuilder.setFind(find);
        tacletBuilder.setApplicationRestriction(RewriteTaclet.ANTECEDENT_POLARITY);
        RewriteTacletGoalTemplate goal =
                new RewriteTacletGoalTemplate(replacewith);
        tacletBuilder.addTacletGoalTemplate(goal);
        tacletBuilder.addRuleSet(new RuleSet(new Name("concrete")));
        tacletBuilder.setSurviveSmbExec(true);

        return tacletBuilder.getTaclet();
    }
}
