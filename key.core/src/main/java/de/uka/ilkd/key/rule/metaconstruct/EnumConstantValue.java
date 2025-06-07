/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.Name;
import org.key_project.logic.op.Operator;

/**
 * resolve a program variable to an integer literal.
 *
 * If the PV is a enum constant, its index in the enum constant array is returned. If the PC is a
 * reference to the nextToCreate field than the number of enum constants is returned.
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
     * If the program variable is the nextToCreate-field resolve it to the number of enum constants
     * of the container. Otherwise result in the index of the constant.
     *
     * @throws IllegalArgumentException if the pv is neither a constant nor ntc.
     */
    public JTerm transform(JTerm term, SVInstantiations svInst, Services services) {
        term = term.sub(0);
        Operator op = term.op();

        if (op instanceof ProgramVariable pv) {
            int value;

            // String varname = pv.getProgramElementName().getProgramName();

            if (false) {// varname.endsWith(ImplicitFieldAdder.IMPLICIT_NEXT_TO_CREATE)) {//TODO
                // <nextToCreate>
                if (pv.getContainerType().getJavaType() instanceof EnumClassDeclaration ecd) {
                    value = ecd.getNumberOfConstants();
                } else {
                    throw new IllegalArgumentException(term + " is not in an enum type.");
                }
            } else {
                // enum constant
                value = EnumClassDeclaration.indexOf(pv);
                if (value == -1) {
                    throw new IllegalArgumentException(term + " is not an enum constant");
                }
            }

            final IntLiteral valueLiteral = KeYJavaASTFactory.intLiteral(value);
            term = services.getTypeConverter().convertToLogicElement(valueLiteral);
        }

        return term;
    }

}
