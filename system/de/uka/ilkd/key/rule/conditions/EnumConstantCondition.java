// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

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
 * ensures that the given instantiation for the schemavariable denotes a
 * constant of an enum type.
 * 
 * @author mulbrich
 * @since 2006-12-04
 * @version 2006-12-11
 */
public class EnumConstantCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;

    /**
     * the static reference condition checks if a suggested
     * instantiation for a schema variable denotes a reference to 
     * an enum constant.
     */
    public EnumConstantCondition (SchemaVariable reference) {
	this.reference = reference;
    }

    /**
     * tests if the instantiation suggestion is an enum constant
     * @param var the template Variable to be instantiated
     * @param subst the SVSubstitute to be mapped to var
     * @param svInst the SVInstantiations that are already known to be
     * needed
     * @return true iff condition is fulfilled
     */
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {

        if (var == reference) {
            // new ObjectInspector(var).setVisible(true);
            // new ObjectInspector(subst).setVisible(true);
            ProgramVariable progvar;

            if (subst instanceof FieldReference) {
                progvar = ((FieldReference) subst).getProgramVariable();
            } else if (subst instanceof Term
                    && ((Term) subst).op() instanceof ProgramVariable) {
                progvar = (ProgramVariable) ((Term) subst).op();
            } else {
                return false;
            }

            return EnumClassDeclaration.isEnumConstant(progvar);

        }
        return true;
    }

    public String toString () {
	return "\\enumConstant(" + reference + ")";
    }

}
