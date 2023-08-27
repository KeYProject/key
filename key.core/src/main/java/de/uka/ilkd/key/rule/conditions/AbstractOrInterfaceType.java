/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a given type denotes an abstract class or interface type.
 */
public final class AbstractOrInterfaceType extends VariableConditionAdapter {

    private final TypeResolver resolver;
    private final boolean negated;

    public AbstractOrInterfaceType(TypeResolver tr, boolean negation) {
        this.resolver = tr;
        this.negated = negation;
    }

    public boolean isNegated() {
        return negated;
    }

    public TypeResolver getTypeResolver() {
        return resolver;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute instCandidate, SVInstantiations instMap,
            Services services) {
        final Sort sort = resolver.resolveSort(var, instCandidate, instMap, services);

        final boolean isAbstractOrInterface = sort.isAbstract();

        return negated != isAbstractOrInterface;
    }


    @Override
    public String toString() {
        String prefix = negated ? "\\not" : "";
        return prefix + "\\isAbstractOrInterface (" + resolver + ")";
    }
}
