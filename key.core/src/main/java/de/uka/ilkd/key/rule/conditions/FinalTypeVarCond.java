/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.ClassType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;


/**
 * This variable condition checks if a given type denotes a final type.
 *
 * Final types are either primitive types or classes that are declared final or arrays of final
 * types.
 *
 * @author Mattias Ulbrich
 */
public final class FinalTypeVarCond extends VariableConditionAdapter {

    private final TypeResolver resolver;
    private final boolean negated;

    /**
     * Instantiates a new final-type condition.
     *
     * @param tr the type resolver for the type to check
     * @param negation whether the condition is negated ({@code \not isFinal})
     */
    public FinalTypeVarCond(TypeResolver tr, boolean negation) {
        this.resolver = tr;
        this.negated = negation;
    }

    public boolean isNegated() {
        return negated;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap,
            Services services) {
        Sort sort = resolver.resolveSort(var, instCandidate, instMap, services);
        while (sort instanceof ArraySort arraySort) {
            sort = arraySort.elementSort();
        }

        Type type = services.getJavaInfo().getKeYJavaType(sort).getJavaType();

        boolean isFinal;
        if (type instanceof PrimitiveType) {
            isFinal = true;
        } else if (type instanceof ClassType classType) {
            isFinal = classType.isFinal();
        } else {
            isFinal = false;
        }

        return negated != isFinal;
    }


    @Override
    public String toString() {
        String prefix = negated ? "\\not" : "";
        return prefix + "\\isFinal (" + resolver + ")";
    }
}
