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
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 *
 * @author christoph
 */
@NullMarked
public class LoopInfFlowUnfoldTacletBuilder extends AbstractInfFlowUnfoldTacletBuilder {

    private @Nullable LoopSpecification loopInv;
    private @Nullable ExecutionContext executionContext;
    private @Nullable JTerm guard;


    public LoopInfFlowUnfoldTacletBuilder(Services services) {
        super(services);
    }


    public void setLoopInv(LoopSpecification loopInv) {
        this.loopInv = loopInv;
    }


    public void setExecutionContext(ExecutionContext context) {
        this.executionContext = context;
    }


    public void setGuard(JTerm guard) {
        this.guard = guard;
    }


    @Override
    Name getTacletName() {
        final LoopSpecification loop = requireLoopInv();
        return MiscTools.toValidTacletName(UNFOLD + unfoldCounter + " of " + loop.getUniqueName());
    }


    @Override
    JTerm createFindTerm(IFProofObligationVars ifVars) {
        InfFlowPOSnippetFactory f = POSnippetFactory.getInfFlowFactory(requireLoopInv(), ifVars.c1,
            ifVars.c2, requireExecutionContext(), requireGuard(), services);
        return f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
    }


    private LoopSpecification requireLoopInv() {
        final LoopSpecification loop = loopInv;
        if (loop == null) {
            throw new NullPointerException(
                "No loop invariant for building the information flow loop unfold taclet.");
        }
        return loop;
    }


    private ExecutionContext requireExecutionContext() {
        final ExecutionContext context = executionContext;
        if (context == null) {
            throw new NullPointerException(
                "No execution context for building the information flow loop unfold taclet.");
        }
        return context;
    }


    private JTerm requireGuard() {
        final JTerm g = guard;
        if (g == null) {
            throw new NullPointerException(
                "No guard for building the information flow loop unfold taclet.");
        }
        return g;
    }
}
