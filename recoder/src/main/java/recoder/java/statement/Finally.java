/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.*;

/**
 * Finally.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Finally extends Branch {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7603770274498242193L;
    /**
     * Body.
     */

    protected StatementBlock body;

    /**
     * Finally.
     */

    public Finally() {
        super();
    }

    /**
     * Finally.
     *
     * @param body a statement.
     */

    public Finally(StatementBlock body) {
        setBody(body);
        makeParentRoleValid();
    }

    /**
     * Finally.
     *
     * @param proto a finally.
     */

    protected Finally(Finally proto) {
        super(proto);
        if (proto.body != null) {
            body = proto.body.deepClone();
        }
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Finally deepClone() {
        return new Finally(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (body != null) {
            body.setStatementContainer(this);
        }
    }

    /**
     * Replace a single child in the current node. The child to replace is matched by identity and
     * hence must be known exactly. The replacement element can be null - in that case, the child is
     * effectively removed. The parent role of the new child is validated, while the parent link of
     * the replaced child is left untouched.
     *
     * @param p the old child.
     * @param p the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (body == p) {
            StatementBlock r = (StatementBlock) q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (body != null) {
            result++;
        }
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (body != null) {
            if (index == 0) {
                return body;
            }
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: body
        if (body == child) {
            return 0;
        }
        return -1;
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? 1 : 0;
    }

    /*
     * Return the statement at the specified index in this node's "virtual" statement array. @param
     * index an index for a statement. @return the statement with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get body.
     *
     * @return the statement.
     */

    public Statement getBody() {
        return body;
    }

    /**
     * Set body; must be a {@link recoder.java.StatementBlock}.
     *
     * @param statement a StatementBlock.
     */

    public void setBody(Statement statement) {
        body = (StatementBlock) statement;
    }

    /**
     * Set parent.
     *
     * @param parent a try.
     */

    public void setParent(Try parent) {
        this.parent = parent;
    }

    public SourceElement getLastElement() {
        return body;
    }

    public void accept(SourceVisitor v) {
        v.visitFinally(this);
    }
}
