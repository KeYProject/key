// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if a type is an enum type.
 * 
 * @author mulbrich
 * @since 2006-12-14
 */
public class EnumTypeCondition extends VariableConditionAdapter {

    private TypeResolver resolver;

    // if negated==true than the result is negated, ie. true is returned iff var
    // is NOT an array
    private boolean negated;

    /**
     * creates a condition that checks if a type is a EnumDeclaration
     * 
     * @param resolver
     *            the type resolver to be checked
     * @param negated
     *            shlould the result be negated
     */
    public EnumTypeCondition(TypeResolver resolver, boolean negated) {
        this.resolver = resolver;
        this.negated = negated;
    }

    /**
     * checks if the condition for a correct instantiation is fulfilled
     * 
     * @param var
     *            the template Variable to be instantiated
     * @param candidate
     *            the SVSubstitute which is a candidate for an instantiation of
     *            var
     * @param svInst
     *            the SVInstantiations that are already known to be needed
     * @return true iff condition is fulfilled
     */
    public boolean check(SchemaVariable var, SVSubstitute candidate,
            SVInstantiations svInst, Services services) {

        if (!resolver.isComplete(var, candidate, svInst, services)) {
            // not yet complete
            System.err.println(resolver + " not complete");
            return true;
        } else {
            // complete
            Sort sort = resolver.resolveSort(var, candidate, svInst, services);
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
            return kjt.getJavaType() instanceof EnumClassDeclaration;
        }
    }

    public String toString() {
        return (negated ? "\\not":"") + "\\isEnumType(" + resolver + ")";
    }

}
