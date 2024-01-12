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
 * Do.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Do extends LoopStatement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1933906789623152123L;

    /**
     * Do.
     */

    public Do() {
        // nothing to do
    }

    /**
     * Do.
     *
     * @param guard an expression.
     */

    public Do(Expression guard) {
        super();
        setGuard(guard);
        makeParentRoleValid();
    }

    /**
     * Do.
     *
     * @param guard an expression.
     * @param body a statement.
     */

    public Do(Expression guard, Statement body) {
        super(body);
        setGuard(guard);
        makeParentRoleValid();
    }

    /**
     * Do.
     *
     * @param proto a do.
     */

    protected Do(Do proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Do deepClone() {
        return new Do(this);
    }

    public SourceElement getLastElement() {
        return this;
    }

    /**
     * Is exit condition.
     *
     * @return the boolean value.
     */

    public boolean isExitCondition() {
        return true;
    }

    /**
     * Is checked before iteration.
     *
     * @return the boolean value.
     */

    public boolean isCheckedBeforeIteration() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitDo(this);
    }
}
