/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.sort.Sort;

/**
 * Variable condition that enforces a given generic sort to be instantiated with the type of a field
 * constant.
 *
 * The condition can only be fulfilled if the given field term is constant of which the referred
 * type is known.
 */
public final class FieldTypeToSortCondition implements VariableCondition {

    private final SchemaVariable exprOrTypeSV;
    private final GenericSort sort;

    public FieldTypeToSortCondition(final OperatorSV exprOrTypeSV, final GenericSort sort) {
        this.exprOrTypeSV = exprOrTypeSV;
        this.sort = sort;
        assert checkSortedSV(exprOrTypeSV);
    }

    public static boolean checkSortedSV(final OperatorSV exprOrTypeSV) {
        final Sort svSort = exprOrTypeSV.sort();
        return svSort == ProgramSVSort.EXPRESSION || svSort == ProgramSVSort.SIMPLEEXPRESSION
                || svSort == ProgramSVSort.NONSIMPLEEXPRESSION || svSort == ProgramSVSort.TYPE
                || exprOrTypeSV.arity() == 0;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SVSubstitute svSubst,
            MatchConditions matchCond, Services services) {

        if (var != exprOrTypeSV) {
            return matchCond;
        }

        final SVInstantiations inst = matchCond.getInstantiations();

        if (svSubst instanceof Term) {
            Operator op = ((Term) svSubst).op();
            if (op instanceof JFunction) {
                HeapLDT.SplitFieldName split = HeapLDT.trySplitFieldName(op);
                if (split == null) {
                    return null;
                }

                ProgramVariable attribute =
                    services.getJavaInfo().getAttribute(split.attributeName(), split.className());

                if (attribute == null) {
                    return null;
                }

                Sort targetSort = attribute.getKeYJavaType().getSort();

                return matchCond.setInstantiations(inst.add(
                    GenericSortCondition.createIdentityCondition(sort, targetSort), services));
            }
        }

        return null;
    }

    @Override
    public String toString() {
        return "\\fieldType(" + exprOrTypeSV + ", " + sort + ")";
    }
}
