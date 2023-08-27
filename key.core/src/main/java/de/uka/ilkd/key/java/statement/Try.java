/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Try.
 *
 * @author <TT>AutoDoc</TT>
 */
public class Try extends BranchStatement implements StatementContainer, ProgramPrefix {

    /**
     * Body.
     */

    private final StatementBlock body;

    /**
     * Branches.
     */

    private final ImmutableArray<Branch> branches;

    private final MethodFrame innerMostMethodFrame;

    private final int prefixLength;

    /**
     * Try.
     *
     * @param body a statement block.
     */

    public Try(StatementBlock body) {
        this.body = body;
        this.branches = null;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    /**
     * Try.
     *
     * @param body a statement block.
     * @param branches a branch array.
     */

    public Try(StatementBlock body, Branch[] branches) {
        this.body = body;
        this.branches = new ImmutableArray<>(branches);
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    /**
     * Try.
     *
     * @param body a statement block.
     * @param branches a branch array.
     */

    public Try(StatementBlock body, ImmutableArray<Branch> branches) {
        this.body = body;
        this.branches = branches;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    /**
     * Try.
     *
     * @param children a list with all children
     */

    public Try(ExtList children) {
        super(children);
        this.body = children.get(StatementBlock.class);
        this.branches = new ImmutableArray<>(children.collect(Branch.class));
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();

    }

    @Override
    public boolean hasNextPrefixElement() {
        return !body.isEmpty() && body.getStatementAt(0) instanceof ProgramPrefix;
    }

    @Override
    public ProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (ProgramPrefix) body.getStatementAt(0);
        } else {
            throw new IndexOutOfBoundsException("No next prefix element " + this);
        }
    }

    @Override
    public ProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : this;
    }

    @Override
    public int getPrefixLength() {
        return prefixLength;
    }

    @Override
    public MethodFrame getInnerMostMethodFrame() {
        return innerMostMethodFrame;
    }

    @Override
    public ImmutableArray<ProgramPrefix> getPrefixElements() {
        return StatementBlock.computePrefixElements(body.getBody(), this);
    }


    public SourceElement getFirstElement() {
        return body.getFirstElement();
    }


    public SourceElement getLastElement() {
        return getChildAt(getChildCount() - 1).getLastElement();
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
        if (branches != null) {
            result += branches.size();
        }
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
        if (body != null) {
            if (index == 0) {
                return body;
            }
            index--;
        }
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get body.
     *
     * @return the statement block.
     */

    public StatementBlock getBody() {
        return body;
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
     * Return the statement at the specified index in this node's "virtual" statement array.
     *
     * @param index an index for a statement.
     *
     * @return the statement with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */

    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of branches in this container.
     *
     * @return the number of branches.
     */

    public int getBranchCount() {
        return (branches != null) ? branches.size() : 0;
    }

    /**
     * Return the branch at the specified index in this node's "virtual" branch array.
     *
     * @param index an index for a branch.
     * @return the branch with the given index.
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */

    public Branch getBranchAt(int index) {
        if (branches != null) {
            return branches.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Return the branch array wrapper
     *
     * @return the array wrapper of the branches
     */
    public ImmutableArray<Branch> getBranchList() {
        return branches;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnTry(this);
    }

    public PosInProgram getFirstActiveChildPos() {
        return body.isEmpty() ? PosInProgram.TOP : PosInProgram.ZERO_ZERO;
    }
}
