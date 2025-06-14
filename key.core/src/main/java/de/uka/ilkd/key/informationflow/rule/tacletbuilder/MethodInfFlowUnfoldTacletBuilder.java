/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;


/**
 *
 * @author christoph
 */
public class MethodInfFlowUnfoldTacletBuilder extends AbstractInfFlowUnfoldTacletBuilder {

    private InformationFlowContract contract;


    public MethodInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setContract(InformationFlowContract c) {
        this.contract = c;
    }


    @Override
    Name getTacletName() {
        return MiscTools.toValidTacletName(
            UNFOLD + unfoldCounter + " of " + contract.getTarget().getUniqueName());
    }


    @Override
    JTerm createFindTerm(IFProofObligationVars ifVars) {
        InfFlowPOSnippetFactory f =
            POSnippetFactory.getInfFlowFactory(contract, ifVars.c1, ifVars.c2, services);
        return f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);
    }
}
