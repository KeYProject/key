/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.MiscTools;


/**
 *
 * @author christoph
 */
public class LoopInfFlowUnfoldTacletBuilder extends AbstractInfFlowUnfouldTacletBuilder {

    private LoopInvariant loopInv;
    private ExecutionContext executionContext;


    public LoopInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setLoopInv(LoopInvariant loopInv) {
        this.loopInv = loopInv;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    @Override
    Name getTacletName() {
        return MiscTools.toValidTacletName("unfold computed formula " +
                                           unfoldCounter + " of " +
                                           loopInv.getUniqueName());
    }


    @Override
    Term createFindTerm(IFProofObligationVars ifVars) {
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(loopInv,
                                                   ifVars.c1, ifVars.c2,
                                                   executionContext,
                                                   services);
        return f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
    }
}
