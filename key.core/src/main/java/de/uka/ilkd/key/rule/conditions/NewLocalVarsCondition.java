/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.ProgramList;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.*;

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
        SVInstantiations svInst = matchCond.getInstantiations();
        if (svInst.getInstantiation(varDeclsSV) != null) {
            return matchCond;
        }
        var body = (Statement) svInst.getInstantiation(bodySV);
        if (body == null) {
            return matchCond;
        }

        var vars = MiscTools.getLocalOuts(body, services);
        List<VariableDeclaration> decls = new ArrayList<>(vars.size());
        ImmutableList<Term> updatesBefore = ImmutableSLList.nil();
        ImmutableList<Term> updatesFrame = ImmutableSLList.nil();
        var tb = services.getTermBuilder();
        for (var v : vars) {
            final var newName =
                services.getVariableNamer().getTemporaryNameProposal(v.name() + "_before");
            KeYJavaType type = v.getKeYJavaType();
            var locVar = new LocationVariable(newName, type);
            var spec = new VariableSpecification(locVar);
            int dim = 0;
            if (type.getJavaType() instanceof ArrayType at) {
                dim = at.getDimension();
            }
            decls.add(new LocalVariableDeclaration(new TypeRef(type, dim), spec));
            updatesBefore = updatesBefore.append(tb.elementary(tb.var(locVar), tb.var(v)));
            updatesFrame = updatesFrame.append(tb.elementary(tb.var(v), tb.var(locVar)));
        }
        return matchCond.setInstantiations(
            svInst.add(varDeclsSV, new ProgramList(new ImmutableArray<>(decls)), services)
                    .add(updateBeforeSV, tb.parallel(updatesBefore), services)
                    .add(updateFrameSV, tb.parallel(updatesFrame), services));
    }

    @Override
    public String toString() {
        return "\\newLocalVars(" + varDeclsSV + ", " + updateBeforeSV + ", " + updateFrameSV + ", "
            + bodySV + ")";
    }
}
