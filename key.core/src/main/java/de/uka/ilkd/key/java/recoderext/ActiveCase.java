/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.*;
import recoder.java.statement.EmptyStatement;
import recoder.java.statement.SwitchBranch;
import recoder.list.generic.ASTList;

public class ActiveCase extends SwitchBranch {
    /**
     * serialization id
     */
    private static final long serialVersionID = /* TODO */ 0;

    /**
     * Body.
     */
    protected ASTList<Statement> body;

    /**
     * ActiveCase.
     */
    public ActiveCase() {
        super();
    }

    /**
     * ActiveCase.
     */
    public ActiveCase(ASTList<Statement> body) {
        setBody(body);
        makeParentRoleValid();
    }

    /**
     * Case.
     *
     * @param proto a case.
     */

    protected ActiveCase(ActiveCase proto) {
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

    public ActiveCase deepClone() {
        return new ActiveCase(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (body != null) {
            for (Statement statement : body) {
                statement.setStatementContainer(this);
            }
        }
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (body != null) {
            result += body.size();
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
        int len;
        if (body != null) {
            len = body.size();
            if (len > index) {
                return body.get(index);
            }
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0 (IDX): body
        if (body != null) {
            int index = body.indexOf(child);
            if (index >= 0) {
                return (index << 4);
            }
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
     * @param q the new child.
     * @return true if a replacement has occured, false otherwise.
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        int count;
        if (p == null) {
            throw new NullPointerException();
        }
        count = (body == null) ? 0 : body.size();
        for (int i = 0; i < count; i++) {
            if (body.get(i) == p) {
                if (q == null) {
                    body.remove(i);
                } else {
                    Statement r = (Statement) q;
                    body.set(i, r);
                    r.setStatementContainer(this);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */

    public int getStatementCount() {
        return (body != null) ? body.size() : 0;
    }

    /*
     * Return the statement at the specified index in this node's "virtual" statement array. @param
     * index an index for a statement. @return the statement with the given index. @exception
     * ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * The body may be empty (null), to define a fall-through. Attaching an
     * {@link EmptyStatement}would create a single ";".
     */

    public ASTList<Statement> getBody() {
        return body;
    }

    /**
     * Set body.
     *
     * @param list a statement mutable list.
     */

    public void setBody(ASTList<Statement> list) {
        body = list;
    }

    public void accept(SourceVisitor v) {
        if (v instanceof SourceVisitorExtended e) {
            e.visitActiveCase(this);
        } else {
            throw new IllegalStateException(
                "Method 'accept' not implemented in " + "ActiveCase");
        }
    }

    public SourceElement getLastElement() {
        if (body == null || body.size() == 0) {
            return this;
        }
        return body.get(body.size() - 1).getLastElement();
    }
}
