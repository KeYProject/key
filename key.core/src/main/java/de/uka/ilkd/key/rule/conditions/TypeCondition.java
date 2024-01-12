/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a schemavariable is instantiated with a reference or primitive
 * type
 */
public final class TypeCondition extends VariableConditionAdapter {

    private final TypeResolver resolver;
    private final boolean nonNull;
    private final boolean isReference;


    /**
     * create a type condition
     *
     * @param tr the TypeResolver for the type to be checked
     * @param isReference check for reference or primitive type (weigl: This parameter is used as
     *        negation)
     * @param nonNull if Sort null should be allowed (only important when isReference is set to
     *        true)
     */
    public TypeCondition(TypeResolver tr, boolean isReference, boolean nonNull) {
        this.resolver = tr;
        this.isReference = isReference;
        this.nonNull = nonNull;
    }

    public TypeResolver getResolver() {
        return resolver;
    }

    public boolean getIsReference() {
        return isReference;
    }

    public boolean getNonNull() {
        return nonNull;
    }


    @Override
    public boolean check(SchemaVariable p_var, SVSubstitute candidate, SVInstantiations svInst,
            Services services) {

        if (!resolver.isComplete(p_var, candidate, svInst, services)) {
            // instantiation not yet complete
            return true;
        }
        final Sort s = resolver.resolveSort(p_var, candidate, svInst, services);

        Sort objectSort = services.getJavaInfo().objectSort();

        boolean isProxySort = s instanceof ProxySort;
        if (!isProxySort) {
            // for normal sorts this is ...
            if (isReference) {
                return (s.extendsTrans(objectSort) && !(nonNull && s instanceof NullSort));
            } else {
                return !(s.extendsTrans(objectSort));
            }
        } else {
            // for proxy sorts this is ...
            if (isReference && nonNull) {
                // non-null cannot be guaranteed since there is no lower bound to type var
                return false;
            }
            if (isReference) {
                // one extended sort must have the property and we are fine
                for (Sort extSort : s.extendsSorts()) {
                    // same as:
                    // extends && isReference || !extends && !isReference
                    if (extSort.extendsTrans(objectSort) == isReference) {
                        return true;
                    }
                }
            }
            return false;
        }
    }


    @Override
    public String toString() {
        String prefix = "\\isReference";
        if (isReference && nonNull) {
            prefix += "[non_null]";
        }
        return (isReference ? "" : "\\not") + prefix + "( " + resolver + " )";
    }


    /**
     * @return returns value of <code>resolver</code>.
     */
    public TypeResolver getTypeResolver() { return resolver; }
}
