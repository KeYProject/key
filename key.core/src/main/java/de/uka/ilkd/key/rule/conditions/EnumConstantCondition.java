/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * ensures that the given instantiation for the schemavariable denotes a constant of an enum type.
 *
 * @author mulbrich
 * @since 2006-12-04
 * @version 2006-12-11
 */
public final class EnumConstantCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;

    /**
     * the static reference condition checks if a suggested instantiation for a schema variable
     * denotes a reference to an enum constant.
     */
    public EnumConstantCondition(SchemaVariable reference) {
        this.reference = reference;
    }


    @Override
    public boolean check(SchemaVariable var, SVSubstitute subst, SVInstantiations svInst,
            Services services) {

        if (var == reference) {
            // new ObjectInspector(var).setVisible(true);
            // new ObjectInspector(subst).setVisible(true);
            ProgramVariable progvar;

            if (subst instanceof FieldReference) {
                progvar = ((FieldReference) subst).getProgramVariable();
            } else if (subst instanceof Term && ((Term) subst).op() instanceof ProgramVariable) {
                progvar = (ProgramVariable) ((Term) subst).op();
            } else {
                return false;
            }

            return EnumClassDeclaration.isEnumConstant(progvar);

        }
        return true;
    }


    @Override
    public String toString() {
        return "\\enumConstant(" + reference + ")";
    }
}
