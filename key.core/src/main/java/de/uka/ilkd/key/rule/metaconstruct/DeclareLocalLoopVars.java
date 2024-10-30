/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.ArrayList;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.util.collection.ImmutableMap;

/**
 * A transformer that takes a ProgramSV, which must be instantiated with a map from variable to
 * variable.
 * The key is the original variable; the entry its "before" version.
 * A variable is only a key in the map if it's written to in the loop body.
 */
public class DeclareLocalLoopVars extends ProgramTransformer {
    public static final String NAME = "declare-local-loop-vars";

    public DeclareLocalLoopVars(Expression expr) {
        super(NAME, expr);
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {
        var vars = (ImmutableMap<LocationVariable, LocationVariable>) svInst
                .getInstantiation((ProgramSV) body());
        var decls = new ArrayList<LocalVariableDeclaration>(vars.size());
        for (var elem : vars) {
            var locVar = elem.value();
            assert locVar != null;
            var spec = new VariableSpecification(locVar);
            int dim = 0;
            KeYJavaType type = locVar.getKeYJavaType();
            if (type.getJavaType() instanceof ArrayType at) {
                dim = at.getDimension();
            }
            decls.add(new LocalVariableDeclaration(new TypeRef(type, dim), spec));
        }
        return decls.toArray(new ProgramElement[0]);
    }
}
