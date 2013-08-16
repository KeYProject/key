/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;


/**
 *
 * @author christoph
 */
public class BlockInfFlowUnfouldTacletBuilder extends AbstractInfFlowUnfouldTacletBuilder {

    private BlockContract contract;


    public BlockInfFlowUnfouldTacletBuilder(Services services) {
        super(services);
    }


    public void setContract(BlockContract c) {
        this.contract = c;
    }


    @Override
    Name getTacletName() {
        return MiscTools.toValidTacletName("unfold computed formula " +
                                           unfoldCounter + " of " +
                                           contract.getUniqueName());
    }


    @Override
    Term createFindTerm(IFProofObligationVars ifVars) {
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(contract,
                                                   ifVars.c1, ifVars.c2,
                                                   services);
        return f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);
    }
}
