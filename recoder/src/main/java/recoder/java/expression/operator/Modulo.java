/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Modulo.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Modulo extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7252952240290731650L;

    /**
     * Modulo.
     */

    public Modulo() {
        // nothing to do
    }

    /**
     * Modulo.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public Modulo(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Modulo.
     *
     * @param proto a modulo.
     */

    protected Modulo(Modulo proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Modulo deepClone() {
        return new Modulo(this);
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
        return 2;
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
        v.visitModulo(this);
    }
}
