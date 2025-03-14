/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.util.ArrayList;

import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclarationContainer;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Statement block. taken from COMPOST and changed to achieve an immutable structure
 */
public class StatementBlock extends JavaStatement implements StatementContainer,
        TypeDeclarationContainer, VariableScope, TypeScope, ProgramPrefix {

    /**
     * Body.
     */
    private final ImmutableArray<? extends Statement> body;

    private final int prefixLength;

    private final MethodFrame innerMostMethodFrame;


    public StatementBlock() {
        body = new ImmutableArray<>();
        prefixLength = 1;
        innerMostMethodFrame = null;
    }


    /**
     * Statement block.
     *
     * @param children an ExtList that contains the children
     */
    public StatementBlock(ExtList children) {
        super(children);
        body = new ImmutableArray<>(children.collect(Statement.class));

        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }

    public StatementBlock(ImmutableArray<? extends Statement> as) {
        // check for non-null elements (bug fix)
        Debug.assertDeepNonNull(as, "statement block contructor");
        body = as;
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials(this);
        prefixLength = info.getLength();
        innerMostMethodFrame = info.getInnerMostMethodFrame();
    }


    public StatementBlock(Statement as) {
        this(new ImmutableArray<>(as));
    }

    public StatementBlock(Statement... body) {
        this(new ImmutableArray<>(body));
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }

        final JavaNonTerminalProgramElement jnte = (JavaNonTerminalProgramElement) o;
        if (jnte.getChildCount() != getChildCount()) {
            return false;
        }

        for (int i = 0, cc = getChildCount(); i < cc; i++) {
            if (!getChildAt(i).equals(jnte.getChildAt(i))) {
                return false;
            }
        }

        return (this.getStartPosition().equals(Position.UNDEFINED) || // why do we care here
                                                                      // about position info and
                                                                      // nowhere else?
                                                                      // We also care in
                                                                      // LoopStatement
                jnte.getStartPosition().equals(Position.UNDEFINED)
                || this.getStartPosition().line() == jnte.getStartPosition().line());
    }

    /** computes the prefix elements for the given array of statment block */
    public static ImmutableArray<ProgramPrefix> computePrefixElements(
            ImmutableArray<? extends Statement> b, ProgramPrefix current) {
        final ArrayList<ProgramPrefix> prefix = new ArrayList<>();
        prefix.add(current);

        while (current.hasNextPrefixElement()) {
            current = current.getNextPrefixElement();
            prefix.add(current);
        }

        return new ImmutableArray<>(prefix);
    }

    /**
     * Get body.
     *
     * @return the statement array wrapper.
     */
    public ImmutableArray<? extends Statement> getBody() {
        return body;
    }

    public final boolean isEmpty() {
        return body.isEmpty();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        return body.size();
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
            return body.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */
    public int getStatementCount() {
        return body.size();
    }

    /**
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
     * Get the number of type declarations in this container.
     *
     * @return the number of type declarations.
     */
    public int getTypeDeclarationCount() {
        int count = 0;
        if (body != null) {
            for (int i = body.size() - 1; i >= 0; i -= 1) {
                if (body.get(i) instanceof TypeDeclaration) {
                    count += 1;
                }
            }
        }
        return count;
    }

    /**
     * Return the type declaration at the specified index in this node's "virtual" type declaration
     * array.
     *
     * @param index an index for a type declaration.
     *
     * @return the type declaration with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public TypeDeclaration getTypeDeclarationAt(int index) {
        if (body != null) {
            int s = body.size();
            for (int i = 0; i < s && index >= 0; i++) {
                Statement st = body.get(i);
                if (st instanceof TypeDeclaration) {
                    if (index == 0) {
                        return (TypeDeclaration) st;
                    }
                    index -= 1;
                }
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnStatementBlock(this);
    }

    public SourceElement getFirstElement() {
        if (isEmpty()) {
            return this;
        }
        final SourceElement e = getBody().get(0);
        return (e instanceof StatementBlock) ? e.getFirstElement() : e;
    }

    @Override
    public SourceElement getFirstElementIncludingBlocks() {
        if (isEmpty()) {
            return this;
        } else {
            return getBody().get(0);
        }
    }

    @Override
    public boolean hasNextPrefixElement() {
        return body.size() != 0 && (body.get(0) instanceof ProgramPrefix);
    }

    @Override
    public ProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (ProgramPrefix) body.get(0);
        } else {
            throw new IndexOutOfBoundsException("No next prefix element " + this);
        }
    }

    @Override
    public ProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? ((ProgramPrefix) body.get(0)).getLastPrefixElement() : this;
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
        return computePrefixElements(body, this);
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return isEmpty() ? PosInProgram.TOP : PosInProgram.ZERO;
    }
}
