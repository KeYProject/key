/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.PossibleProgramPrefix;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

public class ActiveCase extends SwitchBranch implements PossibleProgramPrefix {
    /**
     * Body.
     */
    protected final ImmutableArray<? extends Statement> body;

    private final MethodFrame innerMostMethodFrame;

    private final int prefixLength;

    public ActiveCase() {
        this.body = null;
        prefixLength = 0;
        innerMostMethodFrame = null;
    }

    public ActiveCase(Statement[] body) {
        this.body = new ImmutableArray<>(body);
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    public ActiveCase(ImmutableArray<? extends Statement> body) {
        this.body = body;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments,
     *        several of Statement (as the statements for Default)
     */
    public ActiveCase(ExtList children) {
        super(children);
        this.body = new ImmutableArray<>(children.collect(Statement.class));
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments a
     *        Statement (as the statement following case) Must NOT contain: an Expression indicating
     *        the condition of the case as there are classes that are Expression and Statement, so
     *        they might get mixed up. Use the second parameter of this constructor for the
     *        expression.
     */
    public ActiveCase(ExtList children, PositionInfo pos) {
        super(children, pos);
        this.body = new ImmutableArray<>(children.collect(Statement.class));
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
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
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        int len;
        if (body != null) {
            len = body.size();
            if (len > index) {
                return body.get(index);
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public SourceElement getFirstElement() {
        if (body.isEmpty())
            return this;
        return body.get(0);
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
     * Return the statement at the specified index in this node's "virtual" statement array.
     *
     * @param index an index for a statement.
     *
     * @return the statement with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public Statement getStatementAt(int index) {
        if (body != null) {
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * The body may be empty (null), to define a fall-through. Attaching an {@link EmptyStatement}
     * would create a single ";".
     */
    public ImmutableArray<? extends Statement> getBody() {
        return body;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnActiveCase(this);
    }

    @Override
    public boolean isPrefix() {
        return body != null && !body.isEmpty();
    }

    @Override
    public boolean hasNextPrefixElement() {
        return body != null && !body.isEmpty() && body.get(0) instanceof PossibleProgramPrefix;
    }

    @Override
    public PossibleProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (PossibleProgramPrefix) body.get(0);
        } else {
            throw new IndexOutOfBoundsException("No next prefix element " + this);
        }
    }

    @Override
    public PossibleProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : this;
    }

    @Override
    public ImmutableArray<PossibleProgramPrefix> getPrefixElements() {
        return StatementBlock.computePrefixElements(this);
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return body.isEmpty() ? PosInProgram.TOP : PosInProgram.ZERO;
    }

    @Override
    public int getPrefixLength() {
        return prefixLength;
    }

    @Override
    public MethodFrame getInnerMostMethodFrame() {
        return innerMostMethodFrame;
    }
}
