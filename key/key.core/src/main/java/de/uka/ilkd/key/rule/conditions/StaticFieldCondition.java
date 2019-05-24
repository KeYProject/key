// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if the instantiation of a schemavariable (of
 * type Field) refers to a Java field declared as "static".
 *
 * The negated condition is true if the instantiation refers to an instance
 * (non-static) field.
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
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
                         SVInstantiations instMap, Services services) {
        final Object o = instMap.getInstantiation(field);
        if (o == null || !(o instanceof Term)) {
            return false;
        }
        final Term f = (Term)o;
        final Operator op = f.op();
        if (op instanceof Function) {
            final String name = op.name().toString();

            // check for normal attribute
            int endOfClassName = name.indexOf("::$");

            int startAttributeName = endOfClassName + 3;


            if ( endOfClassName < 0) {
                // not a normal attribute, maybe an implicit attribute like <created>?
                endOfClassName = name.indexOf("::<");
                startAttributeName = endOfClassName + 2;
            }

            if ( endOfClassName < 0 ) {
                return false;
            }

            final String className     = name.substring(0, endOfClassName);
            final String attributeName = name.substring(startAttributeName);

            final ProgramVariable attribute =
                    services.getJavaInfo().getAttribute(attributeName, className);

            if (attribute == null) {
                return false;
            }
            final boolean result = attribute.isStatic();
            return !negated ? result : !result;
        }
        return false;
    }

    @Override
    public String toString() {
        return (negated ? "\\not":"") + "\\isStaticField(" + field + ")";
    }
}