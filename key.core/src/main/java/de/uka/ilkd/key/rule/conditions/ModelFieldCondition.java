/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if the instantiation of a schemavariable (of
 * type Field) refers to a Java field declared as "model".
 *
 * The negated condition is true if the instantiation refers to an instance
 * or static or ghost field.
 *
 * @author Mattias Ulbrich
 *
 * @see StaticReferenceCondition
 */
public class ModelFieldCondition extends VariableConditionAdapter {

    private final SchemaVariable field;
    private final boolean negated;

    public ModelFieldCondition(SchemaVariable field, boolean negated) {
        this.field = field;
        this.negated = negated;
    }

    @Override
    public boolean check(SchemaVariable var, SVSubstitute subst,
            SVInstantiations instMap, Services services) {

        if (var == field) {
            ProgramVariable attribute;
            if (subst instanceof FieldReference) {
                attribute = ((FieldReference) subst).getProgramVariable();
            } else if (subst instanceof ProgramVariable) {
                attribute = (ProgramVariable) subst;
            } else {
                return !negated;
            }

            return (negated ^ attribute.isModel()) &&
                    !(attribute instanceof ProgramConstant);
        }
        return true;
    }

    @Override
    public String toString() {
        return (negated ? "\\not" : "") + "\\isModelField(" + field + ")";
    }
}
