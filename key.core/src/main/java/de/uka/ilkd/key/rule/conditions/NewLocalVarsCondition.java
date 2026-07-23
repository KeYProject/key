/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.abstraction.*;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.reference.TypeRef;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.ListInstantiation;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
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
    public MatchResultInfo check(SchemaVariable var, SyntaxElement instCandidate,
            MatchResultInfo matchCond, LogicServices lServices) {
        var services = (Services) lServices;
        var svInst = matchCond.getInstantiations();
        if (svInst.getInstantiation(varDeclsSV) != null) {
            return matchCond;
        }
        var body = (Statement) svInst.getInstantiation(bodySV);
        if (body == null) {
            return matchCond;
        }

        var vars = MiscTools.getLocalOuts(body, services);
        List<VariableDeclaration> decls = new ArrayList<>(vars.size());
        ImmutableList<JTerm> updatesBefore = ImmutableList.nil();
        ImmutableList<JTerm> updatesFrame = ImmutableList.nil();
        var tb = services.getTermBuilder();
        // Names of "before" variables generated within this single application; needed because
        // the new variables are not yet registered in the namespaces while we build them.
        final Set<String> reserved = new HashSet<>();
        for (var v : vars) {
            // Deterministically derive a unique name from the current proof state instead of
            // using getVariableNamer().getTemporaryNameProposal(), which appends a '#'-index
            // taken from a proof-global counter. That counter is advanced as a side effect of
            // (speculative) taclet matching, so the number of increments differs between a
            // freshly created proof and a reloaded/pruned-and-reapplied one. The resulting name
            // mismatch (e.g. k_before#0 vs. k_before#1) breaks the slicing mechanism, which
            // relies on formula equivalence across reloads. See issue #3834.
            final var newName = uniqueBeforeName(v.name() + "_before", services, reserved);
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
            ((SVInstantiations) svInst)
                    .add(varDeclsSV,
                        new ListInstantiation<>(new ImmutableArray<>(decls),
                            VariableDeclaration.class),
                        services)
                    .add(updateBeforeSV, tb.parallel(updatesBefore), services)
                    .add(updateFrameSV, tb.parallel(updatesFrame), services));
    }

    /**
     * Produces a fresh {@link ProgramElementName} for a "before" variable that is deterministic
     * w.r.t. the current proof state. The name is unique with respect to all current namespaces of
     * {@code services} as well as the names already handed out within the current rule application
     * ({@code reserved}). Unlike
     * {@link de.uka.ilkd.key.logic.VariableNamer#getTemporaryNameProposal(String)}, this does not
     * depend on a mutable proof-global counter, so it stays stable across proof reloads and
     * prune/reapply cycles (issue #3834).
     *
     * @param basename the desired base name, e.g. {@code "k_before"}
     * @param services the services whose namespaces are consulted for collisions
     * @param reserved names already used within the current application; the chosen name is added
     * @return a fresh, collision-free name
     */
    private static ProgramElementName uniqueBeforeName(String basename, Services services,
            Set<String> reserved) {
        final String candidate =
            TermBuilder.freeName(basename, services.getNamespaces(), reserved);
        reserved.add(candidate);
        return new ProgramElementName(candidate);
    }

    @Override
    public String toString() {
        return "\\newLocalVars(" + varDeclsSV + ", " + updateBeforeSV + ", " + updateFrameSV + ", "
            + bodySV + ")";
    }
}
