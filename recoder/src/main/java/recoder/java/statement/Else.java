/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.ProgramElement;
import recoder.java.SourceElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;

/**
 * Else.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Else extends Branch {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 5468467558759778758L;
    /**
     * Body.
     */

    protected Statement body;

    /**
     * Else.
     */

    public Else() {
        super();
    }

    /**
     * Else.
     *
     * @param body a statement.
     */

    public Else(Statement body) {
        setBody(body);
        makeParentRoleValid();
    }

    /**
     * Else.
     *
     * @param proto an else.
     */

    protected Else(Else proto) {
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

    public Else deepClone() {
        return new Else(this);
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

    public SourceElement getLastElement() {
        return body.getLastElement();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (body != null) ? 1 : 0;
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
            Statement r = (Statement) q;
            body = r;
            if (r != null) {
                r.setStatementContainer(this);
            }
            return true;
        }
        return false;
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
     * The body may be empty (null), to define a fall-through. Attaching an
     * {@link EmptyStatement}would create a single ";".
     */

    public Statement getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param statement a statement.
     */

    public void setBody(Statement statement) {
        body = statement;
    }

    /**
     * Set parent.
     *
     * @param parent an if.
     */

    public void setParent(If parent) {
        this.parent = parent;
    }

    public void accept(SourceVisitor v) {
        v.visitElse(this);
    }
}
