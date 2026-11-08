/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.conditions;

import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * This variable condition checks if an array component is of reference type
 */
@NullMarked
public final class ArrayComponentTypeCondition extends VariableConditionAdapter {

    private final SchemaVariable var;
    private final boolean checkReferenceType;



    /**
     * creates an instance of this condition checking if array var has reference or primitive
     * component type depending on the value of <code>checkReferenceType</code>
     *
     * @param var the SchemaVariable to be checked
     * @param checkReferenceType the boolean flag which when is set (<tt>true</tt>) FIXME weigl:
     *        this is not true! checkReferenceType is just the negated flag. checks for reference
     *        otherwise for primitive type
     */
    public ArrayComponentTypeCondition(SchemaVariable var, boolean checkReferenceType) {
        this.var = var;
        this.checkReferenceType = checkReferenceType;
    }

    public boolean isCheckReferenceType() {
        return checkReferenceType;
    }


    @Override
    public boolean check(@Nullable SchemaVariable var, @Nullable SyntaxElement candidate,
            SVInstantiations svInst,
            Services services) {
        if (var != this.var) {
            return true;
        }
        Sort s = null;
        if (candidate instanceof JTerm) {
            s = ((JTerm) candidate).sort();
        } else if (candidate instanceof Expression) {
            s = Objects.requireNonNull(
                ((Expression) candidate).getKeYJavaType(services, svInst.getExecutionContext()),
                "no KeYJavaType for expression candidate").getSort();
        } else if (candidate instanceof TypeReference) {
            s = Objects.requireNonNull(((TypeReference) candidate).getKeYJavaType(),
                "no KeYJavaType for type-reference candidate").getSort();
        }

        if (!(s instanceof ArraySort)) {
            return false;
        }
        return !(((ArraySort) s).elementSort().extendsTrans(services.getJavaInfo().objectSort()))
                ^ checkReferenceType;
    }


    @Override
    public String toString() {
        return (checkReferenceType ? "" : " \\not ") + "\\isReferenceArray(" + var + ")";
    }

    public SchemaVariable getVar() {
        return var;
    }
}
