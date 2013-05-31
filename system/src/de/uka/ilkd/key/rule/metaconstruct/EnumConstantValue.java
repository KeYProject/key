// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * resolve a program variable to an integer literal.
 * 
 * If the PV is a enum constant, its index in the enum constant array is
 * returned. If the PC is a reference to the nextToCreate field than the number
 * of enum constants is returned.
 * 
 * @author mulbrich
 */
public final class EnumConstantValue extends AbstractTermTransformer {

    public EnumConstantValue() {
        super(new Name("#enumconstantvalue"), 1);
    }

    /**
     * calculates the resulting term.
     * 
     * If the program variable is the nextToCreate-field resolve it to the
     * number of enum constants of the container. Otherwise result in the index
     * of the constant.
     * 
     * @throws IllegalArgumentException
     *             if the pv is neither a constant nor ntc.
     */
    public Term transform(Term term, SVInstantiations svInst, Services services) {
        term = term.sub(0);
        Operator op = term.op();

        if (op instanceof ProgramVariable) {
            int value;

            ProgramVariable pv = (ProgramVariable) op;
            String varname = pv.getProgramElementName().getProgramName();

            if (false){//varname.endsWith(ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE)) {//TODO
                // <nextToCreate>
                if (pv.getContainerType().getJavaType() instanceof EnumClassDeclaration) {
                    EnumClassDeclaration ecd = (EnumClassDeclaration) pv
                            .getContainerType().getJavaType();
                    value = ecd.getNumberOfConstants();
                } else {
                    throw new IllegalArgumentException(term
                            + " is not in an enum type.");
                }
            } else {
                // enum constant
                value = EnumClassDeclaration.indexOf(pv);
                if(value == -1)
                    throw new IllegalArgumentException(term + " is not an enum constant");
            }

            term = services.getTypeConverter().convertToLogicElement(new IntLiteral(value));
        }   

        return term;
    }

}
