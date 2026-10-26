/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.rule.tacletbuilder;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.informationflow.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.informationflow.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 *
 * @author christoph
 */
@NullMarked
public class BlockInfFlowUnfoldTacletBuilder extends AbstractInfFlowUnfoldTacletBuilder {

    private @Nullable BlockContract contract;
    private @Nullable ExecutionContext executionContext;


    public BlockInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setContract(BlockContract c) {
        this.contract = c;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    @Override
    Name getTacletName() {
        return MiscTools.toValidTacletName(UNFOLD + unfoldCounter + " of " + requireContract()
                .getUniqueName());
    }


    @Override
    JTerm createFindTerm(IFProofObligationVars ifVars) {
        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(requireContract(),
            ifVars.c1, ifVars.c2, requireExecutionContext(), services);
        return f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_BLOCK_WITH_PRE_RELATION);
    }


    private BlockContract requireContract() {
        final BlockContract c = contract;
        if (c == null) {
            throw new NullPointerException(
                "No contract for building the information flow block unfold taclet.");
        }
        return c;
    }


    private ExecutionContext requireExecutionContext() {
        final ExecutionContext context = executionContext;
        if (context == null) {
            throw new NullPointerException(
                "No execution context for building the information flow block unfold taclet.");
        }
        return context;
    }
}
