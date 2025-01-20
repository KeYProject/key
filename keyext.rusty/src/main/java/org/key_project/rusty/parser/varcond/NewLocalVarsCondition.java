/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import java.util.ArrayList;
import java.util.List;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.pat.BindingPattern;
import org.key_project.rusty.ast.stmt.LetStatement;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.VariableCondition;
import org.key_project.rusty.rule.inst.ProgramList;
import org.key_project.rusty.util.MiscTools;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * For the loop scope rule, if a local program variable that may be altered by the loop body appears
 * in the frame condition,
 * it is necessary to use the value <i>before</i> the loop first executes in the frame condition.
 * <br>
 * To achieve this, this condition generates (1) the "before" version of each variable that may be
 * written to by the loop
 * {@link MiscTools#getLocalOuts(ProgramElement, Services)}; (2) an update storing the value of each
 * such PV in its "before" version,
 * i.e., {@code {...||i_before := i||...}}; (3) the reverse of the update, to be applied to the
 * frame condition, i.e.,
 * {@code {...||i := i_before||...}}.
 */
public class NewLocalVarsCondition implements VariableCondition {
    /**
     * A SV that will store variable declarations for the "before" version of variables.
     */
    private final SchemaVariable varDeclsSV;
    /**
     * Will store the update {@code {...||i_before := i||...}}.
     */
    private final SchemaVariable updateBeforeSV;
    /**
     * Will store the update {@code {...||i := i_before||...}}.
     */
    private final SchemaVariable updateFrameSV;
    /**
     * The loop body.
     */
    private final SchemaVariable bodySV;

    public NewLocalVarsCondition(SchemaVariable varDeclsSV, SchemaVariable updateBeforeSV,
            SchemaVariable updateFrameSV, SchemaVariable bodySV) {
        this.varDeclsSV = varDeclsSV;
        this.updateBeforeSV = updateBeforeSV;
        this.updateFrameSV = updateFrameSV;
        this.bodySV = bodySV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions matchCond, Services services) {
        var svInst = matchCond.getInstantiations();
        if (svInst.getInstantiation(varDeclsSV) != null) {
            return matchCond;
        }
        var body = (Expr) svInst.getInstantiation(bodySV);
        if (body == null) {
            return matchCond;
        }

        var vars = MiscTools.getLocalOuts(body, services);
        List<LetStatement> decls = new ArrayList<>(vars.size());
        ImmutableList<Term> updatesBefore = ImmutableSLList.nil();
        ImmutableList<Term> updateFrames = ImmutableSLList.nil();
        var tb = services.getTermBuilder();

        for (var v : vars) {
            final var newName =
                services.getVariableNamer().getTemporaryNameProposal(v.name() + "_before");
            var type = v.getKeYRustyType();
            var pv = new ProgramVariable(newName, type);
            decls.add(
                new LetStatement(new BindingPattern(false, false, false, pv, null), null, null));
            updatesBefore = updatesBefore.append(tb.elementary(tb.var(pv), tb.var(v)));
            updateFrames = updateFrames.append(tb.elementary(tb.var(v), tb.var(pv)));
        }
        return matchCond.setInstantiations(
            svInst.add(varDeclsSV, new ProgramList(new ImmutableArray<>(decls)), services)
                    .add(updateBeforeSV, tb.parallel(updatesBefore), services)
                    .add(updateFrameSV, tb.parallel(updateFrames), services));
    }

    @Override
    public String toString() {
        return "\\newLocalVars(" + varDeclsSV + ", " + updateBeforeSV + ", " + updateFrameSV + ", "
            + bodySV + ")";
    }
}
