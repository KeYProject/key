/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.infflow.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 *
 * @author christoph
 */
@NullMarked
public class MethodInfFlowUnfoldTacletBuilder extends AbstractInfFlowUnfoldTacletBuilder {

    private @Nullable InformationFlowContract contract;


    public MethodInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setContract(InformationFlowContract c) {
        this.contract = c;
    }


    @Override
    Name getTacletName() {
        final InformationFlowContract c = requireContract();
        return MiscTools.toValidTacletName(UNFOLD + unfoldCounter + " of " + c.getTarget()
                .getUniqueName());
    }


    @Override
    JTerm createFindTerm(IFProofObligationVars ifVars) {
        final InformationFlowContract c = requireContract();
        InfFlowPOSnippetFactory f =
            POSnippetFactory.getInfFlowFactory(c, ifVars.c1, ifVars.c2, services);
        return f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);
    }


    private InformationFlowContract requireContract() {
        final InformationFlowContract c = contract;
        if (c == null) {
            throw new NullPointerException(
                "No contract for building the information flow unfold taclet.");
        }
        return c;
    }
}
