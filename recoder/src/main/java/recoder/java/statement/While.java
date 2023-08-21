/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.Expression;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;

/**
 * While.
 *
 * @author <TT>AutoDoc</TT>
 */

public class While extends LoopStatement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -8497002453485096424L;

    /**
     * While.
     */

    public While() {
        // nothing to do
    }

    /**
     * While.
     *
     * @param guard an expression.
     */

    public While(Expression guard) {
        setGuard(guard);
        makeParentRoleValid();
    }

    /**
     * While.
     *
     * @param guard an expression.
     * @param body a statement.
     */

    public While(Expression guard, Statement body) {
        super(body);
        setGuard(guard);
        makeParentRoleValid();
    }

    /**
     * While.
     *
     * @param proto a while.
     */

    protected While(While proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public While deepClone() {
        return new While(this);
    }

    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    /**
     * Is exit condition.
     *
     * @return the boolean value.
     */

    public boolean isExitCondition() {
        return false;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */

    public boolean isCheckedBeforeIteration() {
        return true;
    }

    public void accept(SourceVisitor v) {
        v.visitWhile(this);
    }
}
