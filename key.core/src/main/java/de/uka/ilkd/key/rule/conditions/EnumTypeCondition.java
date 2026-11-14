/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This variable condition checks if a type is an enum type.
 *
 * @author mulbrich
 * @since 2006-12-14
 */
@NullMarked
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
    public boolean check(@Nullable SchemaVariable var, @Nullable SyntaxElement candidate,
            SVInstantiations svInst,
            Services services) {

        if (!resolver.isComplete(var, candidate, svInst, services)) {
            // not yet complete
            LOGGER.warn("{} not complete", resolver);
            return true;
        } else {
            // complete
            Sort sort = Objects.requireNonNull(
                resolver.resolveSort(var, candidate, svInst, services),
                "no sort resolved by " + resolver);
            KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
            return Objects.requireNonNull(kjt, "no KeYJavaType for sort " + sort)
                    .getJavaType() instanceof EnumClassDeclaration;
        }
    }


    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\isEnumType(" + resolver + ")";
    }
}
