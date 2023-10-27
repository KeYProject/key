/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.statement;

import recoder.java.*;

/**
 * Labeled statement.
 *
 * @author <TT>AutoDoc</TT>
 */

public class LabeledStatement extends JavaStatement
        implements StatementContainer, NamedProgramElement {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -4621689270408033058L;

    /**
     * Name.
     */

    protected Identifier name;

    /**
     * Body.
     */

    protected Statement body;

    /**
     * Labeled statement.
     */

    public LabeledStatement() {
        // nothing to do
    }

    /**
     * Labeled statement.
     *
     * @param id an identifier.
     */

    public LabeledStatement(Identifier id) {
        setIdentifier(id);
        setBody(getFactory().createEmptyStatement());
        makeParentRoleValid();
    }

    /**
     * Labeled statement.
     *
     * @param id an identifier.
     * @param statement a statement.
     */

    public LabeledStatement(Identifier id, Statement statement) {
        setIdentifier(id);
        setBody(statement);
        makeParentRoleValid();
    }

    /**
     * Labeled statement.
     *
     * @param proto a labeled statement.
     */

    protected LabeledStatement(LabeledStatement proto) {
        super(proto);
        if (proto.name != null) {
            name = proto.name.deepClone();
        }
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

    public LabeledStatement deepClone() {
        return new LabeledStatement(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (name != null) {
            name.setParent(this);
        }
        if (body != null) {
            body.setStatementContainer(this);
        }
    }

    public SourceElement getFirstElement() {
        return getChildAt(0).getFirstElement();
    }

    public SourceElement getLastElement() {
        return body.getLastElement();
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
        if (name == p) {
            Identifier r = (Identifier) q;
            name = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
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
     * Get name.
     *
     * @return the string.
     */

    public final String getName() {
        return (name == null) ? null : name.getText();
    }

    /**
     * Get identifier.
     *
     * @return the identifier.
     */

    public Identifier getIdentifier() {
        return name;
    }

    /**
     * Set identifier.
     *
     * @param id an identifier.
     */

    public void setIdentifier(Identifier id) {
        name = id;
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
     * Set body.
     *
     * @param s a statement.
     */

    public void setBody(Statement s) {
        body = s;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (name != null) {
            result++;
        }
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
        if (name != null) {
            if (index == 0) {
                return name;
            }
            index--;
        }
        if (body != null) {
            if (index == 0) {
                return body;
            }
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: name
        // role 1: body
        if (name == child) {
            return 0;
        }
        if (body == child) {
            return 1;
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

    /**
     * Return the statement at the specified index in this node's "virtual" statement array.
     *
     * @param index an index for a statement.
     * @return the statement with the given index.
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public void accept(SourceVisitor v) {
        v.visitLabeledStatement(this);
    }
}
