/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.jspecify.annotations.Nullable;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.Pair;


/**
 * ensures that the given instantiation for the schemavariable denotes a constant of an enum type.
 *
 * @author mulbrich
 * @since 2006-12-04
 * @version 2006-12-11
 * @version 2025-10-24 Refactored for the "new" heap model.
 */
public final class EnumConstantCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;
    private final GenericSort typeReference;

    /**
     * the static reference condition checks if a suggested instantiation for a schema variable
     * denotes a reference to an enum constant.
     */
    public EnumConstantCondition(GenericSort typeReference, SchemaVariable reference) {
        this.reference = reference;
        this.typeReference = typeReference;
    }


    @Override
    public boolean check(SchemaVariable var, SyntaxElement subst, SVInstantiations svInst,
            Services services) {

        if (var == reference) {
            // try to find the enum constant field
            @Nullable Pair<Integer, IProgramVariable> field = resolveEnumFieldConstant(subst, services);
            if (field == null)
                return false;

            // if there is such a field, check that its type is the right enum type
            KeYJavaType containerType = ((ProgramVariable) field.second).getContainerType();
            Sort typeInst = svInst.getGenericSortInstantiations().getInstantiation(typeReference);
            return containerType.getSort() == typeInst;
        }

        return true;
    }

    // also used in EnumConstantValue
    public static @Nullable Pair<Integer, IProgramVariable> resolveEnumFieldConstant(Object obj, Services services) {
        if(obj instanceof Term term) {
            Operator op = term.op();
            if (op instanceof Function func && func.isUnique()
                    && func.sort() == services.getTypeConverter().getHeapLDT().getFieldSort()
                    && func.name().toString().contains("::")) {
                String funcName = func.name().toString();
                int colon = funcName.indexOf("::$");
                if (colon == -1) {
                    return null;
                }
                String sortName = funcName.substring(0, colon);
                String fieldName = funcName.substring(colon + 3);
                KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sortName);
                if (kjt == null || !(kjt.getJavaType() instanceof EnumClassDeclaration)) {
                    return null;
                }
                EnumClassDeclaration ecd = (EnumClassDeclaration) kjt.getJavaType();
                return ecd.getConstant(fieldName);
            }
        }
        return null;
    }



    @Override
    public String toString() {
        return "\\isEnumConst(" + typeReference + ", " + reference + ")";
    }
}
