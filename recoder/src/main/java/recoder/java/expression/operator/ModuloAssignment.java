/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Modulo assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class ModuloAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 4380772781463528921L;

    /**
     * Modulo assignment.
     */

    public ModuloAssignment() {
        // nothing to do
    }

    /**
     * Modulo assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public ModuloAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Modulo assignment.
     *
     * @param proto a modulo assignment.
     */

    protected ModuloAssignment(ModuloAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ModuloAssignment deepClone() {
        return new ModuloAssignment(this);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 2;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 13;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    public void accept(SourceVisitor v) {
        v.visitModuloAssignment(this);
    }
}
