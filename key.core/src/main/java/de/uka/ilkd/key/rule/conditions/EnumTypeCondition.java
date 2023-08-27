/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This variable condition checks if a type is an enum type.
 *
 * @author mulbrich
 * @since 2006-12-14
 */
public final class EnumTypeCondition extends VariableConditionAdapter {
    private static final Logger LOGGER = LoggerFactory.getLogger(EnumTypeCondition.class);

    private final TypeResolver resolver;
    private final boolean negated;

    /**
     * creates a condition that checks if a type is a EnumDeclaration
     *
     * @param resolver the type resolver to be checked
     * @param negated should the result be negated
     */
    public EnumTypeCondition(TypeResolver resolver, boolean negated) {
        this.resolver = resolver;
        this.negated = negated;
    }


    @Override
    public boolean check(SchemaVariable var, SVSubstitute candidate, SVInstantiations svInst,
            Services services) {

        if (!resolver.isComplete(var, candidate, svInst, services)) {
            // not yet complete
            LOGGER.warn("{} not complete", resolver);
            return true;
        } else {
            // complete
            Sort sort = resolver.resolveSort(var, candidate, svInst, services);
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
            return kjt.getJavaType() instanceof EnumClassDeclaration;
        }
    }


    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\isEnumType(" + resolver + ")";
    }
}
