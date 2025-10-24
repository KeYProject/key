/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.conditions.EnumConstantCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.util.collection.Pair;

/**
 * resolve a program variable to an integer literal.
 *
 * If the PV is a enum constant field constant, its index in the enum constant array is returned.
 * This is the ordinal of the enum constant.
 *
 * @author mulbrich
 */
public final class EnumConstantValue extends AbstractTermTransformer {

    public EnumConstantValue() {
        super(new Name("#enumconstantvalue"), 1);
    }

    /**
     * calculates the resulting term.
     *
     * If the program variable is the nextToCreate-field resolve it to the number of enum constants
     * of the container. Otherwise result in the index of the constant.
     *
     * @throws IllegalArgumentException if the pv is neither a constant nor ntc.
     */
    public JTerm transform(JTerm term, SVInstantiations svInst, Services services) {
        term = term.sub(0);

        @Nullable Pair<Integer, IProgramVariable> enConst = EnumConstantCondition.resolveEnumFieldConstant(term, services);
        if(enConst == null) {
            return term;
        }

        int ordinal = enConst.first;
        return services.getTermBuilder().zTerm(ordinal);
    }

}
