/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.LocationVarMap;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.SyntaxElement;
import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

import org.jspecify.annotations.NonNull;

/**
 * Collects all local variables written to in {@code bodySV} and instantiates {@code varsSV} with a
 * map
 * from these variables to their (newly created, unique) "before" version.
 */
public class NewLocalVarsCondition implements VariableCondition {
    private final SchemaVariable varsSV;
    private final SchemaVariable bodySV;

    public NewLocalVarsCondition(SchemaVariable vars, SchemaVariable body) {
        this.varsSV = vars;
        this.bodySV = body;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions matchCond, Services services) {
        SVInstantiations svInst = matchCond.getInstantiations();
        if (svInst.getInstantiation(varsSV) != null) {
            return matchCond;
        }
        var body = (Statement) svInst.getInstantiation(bodySV);
        if (body == null) {
            return matchCond;
        }

        var vars = MiscTools.getLocalOuts(body, services);
        ImmutableMap<@NonNull LocationVariable, LocationVariable> map =
            DefaultImmutableMap.nilMap();
        for (var v : vars) {
            final var newName =
                services.getVariableNamer().getTemporaryNameProposal(v.name() + "_before");
            KeYJavaType type = v.getKeYJavaType();
            var locVar = new LocationVariable(newName, type);
            map = map.put(v, locVar);
        }
        return matchCond.setInstantiations(svInst.add(varsSV, new LocationVarMap(map), services));
    }

    @Override
    public String toString() {
        return "\\newLocalVars(" + varsSV + ", " + bodySV + ")";
    }
}
