/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.logic.op.OperatorSV;

import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.statement.JavaStatement;

public class StatementSVWrapper extends JavaStatement implements KeYRecoderExtension, SVWrapper {

    /**
     *
     */
    private static final long serialVersionUID = -4062276649575988872L;
    protected final OperatorSV sv;

    protected StatementSVWrapper(StatementSVWrapper proto) {
        super(proto);
        sv = proto.getSV();
    }

    public StatementSVWrapper(OperatorSV sv) {
        this.sv = sv;
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }


    public int getChildPositionCode(ProgramElement child0) {
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
     * @exception ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        return false;
    }


    /**
     * returns a String name of this meta construct.
     */
    public OperatorSV getSV() {
        return sv;
    }


    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */

    public int getStatementCount() {
        return 0;
    }

    /*
     * Return the statement at the specified index in this node's "virtual" statement array.
     *
     * @param index an index for a statement.
     *
     * @return the statement with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public Statement getStatementAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }

    // don't think we need it
    public void accept(SourceVisitor v) {
    }

    public StatementSVWrapper deepClone() {
        return new StatementSVWrapper(sv);
    }


}
