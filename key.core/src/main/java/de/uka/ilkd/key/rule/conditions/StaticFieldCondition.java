/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.SyntaxElement;

/**
 * This variable condition checks if the instantiation of a schemavariable (of type Field) refers to
 * a Java field declared as "static".
 *
 * The negated condition is true if the instantiation refers to an instance (non-static) field.
 *
 * Inspired by {@link de.uka.ilkd.key.rule.conditions.FieldTypeToSortCondition}.
 *
 * @author Michael Kirsten
 */
public class StaticFieldCondition extends VariableConditionAdapter {

    private final SchemaVariable field;
    private final boolean negated;

    public StaticFieldCondition(SchemaVariable field, boolean negated) {
        this.field = field;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SyntaxElement instCandidate, SVInstantiations instMap,
            Services services) {
        final Object o = instMap.getInstantiation(field);
        if (!(o instanceof Term f)) {
            return false;
        }
        final Operator op = f.op();
        if (op instanceof JFunction) {
            HeapLDT.SplitFieldName split = HeapLDT.trySplitFieldName(op);
            if (split == null) {
                return false;
            }

            final ProgramVariable attribute =
                services.getJavaInfo().getAttribute(split.attributeName(), split.className());

            if (attribute == null) {
                return false;
            }
            final boolean result = attribute.isStatic();
            return negated != result;
        }
        return false;
    }

    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\isStaticField(" + field + ")";
    }
}
