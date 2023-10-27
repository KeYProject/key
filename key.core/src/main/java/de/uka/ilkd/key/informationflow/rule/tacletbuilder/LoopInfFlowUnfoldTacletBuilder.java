/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;


/**
 *
 * @author christoph
 */
public class LoopInfFlowUnfoldTacletBuilder extends AbstractInfFlowUnfoldTacletBuilder {

    private LoopSpecification loopInv;
    private ExecutionContext executionContext;
    private Term guard;


    public LoopInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setLoopInv(LoopSpecification loopInv) {
        this.loopInv = loopInv;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    public void setGuard(Term guard) {
        this.guard = guard;
    }


    @Override
    Name getTacletName() {
        return MiscTools
                .toValidTacletName(UNFOLD + unfoldCounter + " of " + loopInv.getUniqueName());
    }


    @Override
    Term createFindTerm(IFProofObligationVars ifVars) {
        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(loopInv, ifVars.c1,
            ifVars.c2, executionContext, guard, services);
        return f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
    }
}
