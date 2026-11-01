/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.ccatch.CcatchNonstandardParameterDeclaration;
import de.uka.ilkd.key.java.ast.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public final class Ccatch extends BranchImp implements ParameterContainer, VariableScope {
    private @Nullable ParameterDeclaration parameter;

    private @Nullable CcatchNonstandardParameterDeclaration nonStdParameter;

    private final StatementBlock body;

    // BranchImp's (PositionInfo, List<Comment>) constructor is over-narrow: it merely forwards to
    // the @Nullable-annotated JavaNonTerminalProgramElement ctor, but BranchImp is outside this
    // wave's file set and cannot be widened here; the convenience ctors
    // Ccatch(ParameterDeclaration,
    // ...) and Ccatch(CcatchNonstandardParameterDeclaration, ...) also legitimately pass null, so
    // these params stay @Nullable and the check is scoped to this ctor.
    @SuppressWarnings("nullness:argument.type.incompatible")
    public Ccatch(@Nullable PositionInfo pi, @Nullable List<Comment> comments,
            @Nullable ParameterDeclaration parameter,
            @Nullable CcatchNonstandardParameterDeclaration nonStdParameter, StatementBlock body) {
        super(pi, comments);
        this.parameter = parameter;
        this.nonStdParameter = nonStdParameter;
        this.body = body;
    }

    /**
     * Ccatch.
     *
     * @param e
     *        a parameter declaration.
     * @param body
     *        a statement.
     */
    public Ccatch(ParameterDeclaration e, StatementBlock body) {
        this(null, null, e, null, body);
    }

    /**
     * Ccatch.
     *
     * @param e
     *        a parameter declaration.
     * @param body
     *        a statement.
     */
    public Ccatch(CcatchNonstandardParameterDeclaration e, StatementBlock body) {
        this(null, null, null, e, body);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children
     *        the children of this AST element as KeY classes. May contain:
     *        Comments, a* ParameterDeclaration (declaring the catched exceptions) a StatementBlock
     *        (as the* action to do when catching)
     */
    public Ccatch(ExtList children) {
        super(children);
        parameter = children.get(ParameterDeclaration.class);
        nonStdParameter =
            children.get(CcatchNonstandardParameterDeclaration.class);
        body = Objects.requireNonNull(children.get(StatementBlock.class),
            "ccatch statement requires a body");
    }

    @Override
    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    public boolean hasParameterDeclaration() {
        return parameter != null;
    }

    public boolean hasNonStdParameterDeclaration() {
        return nonStdParameter != null;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        int result = 0;
        if (hasParameterDeclaration()) {
            result++;
        }
        if (hasNonStdParameterDeclaration()) {
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
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out of bounds
     */
    // the parameter and the non-standard parameter may legitimately be absent (a ccatch declares
    // exactly one of them); the base contract NonTerminalProgramElement.getChildAt(int) is
    // over-narrow; honest @Nullable override per SuperArrayDeclaration precedent (wave 7).
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable ProgramElement getChildAt(int index) {
        if (hasParameterDeclaration()) {
            if (index == 0) {
                return parameter;
            }
            index--;
        }
        if (hasNonStdParameterDeclaration()) {
            if (index == 0) {
                return nonStdParameter;
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

    /**
     * Get the number of statements in this container.
     *
     * @return the number of statements.
     */
    @Override
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
    @Override
    public Statement getStatementAt(int index) {
        if (body != null && index == 0) {
            return body;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of parameters in this container.
     *
     * @return the number of parameters.
     */
    @Override
    public int getParameterDeclarationCount() {
        return (hasParameterDeclaration()) ? 1 : 0;
    }

    /**
     * Return the parameter declaration at the specified index in this node's "virtual" parameter
     * declaration array.
     *
     * @param index
     *        an index for a parameter declaration.
     * @return the parameter declaration with the given index.
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out of bounds.
     */
    // the parameter may be absent (see hasParameterDeclaration()); the base contract
    // ParameterContainer.getParameterDeclarationAt(int) is over-narrow, so the honest @Nullable
    // override is exempted from the check.
    @SuppressWarnings("nullness:override.return.invalid")
    @Override
    public @Nullable ParameterDeclaration getParameterDeclarationAt(int index) {
        if (hasParameterDeclaration() && index == 0) {
            return parameter;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Return the non-standard parameter declaration at the specified index in this node's "virtual"
     * parameter declaration array.
     *
     * @param index
     *        an index for a parameter declaration.
     * @return the parameter declaration with the given index.
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out of bounds.
     */
    public @Nullable CcatchNonstandardParameterDeclaration getNonStdParameterDeclarationAt(
            int index) {
        if (hasNonStdParameterDeclaration() && index == 0) {
            return nonStdParameter;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get body.
     *
     * @return the statement.
     */
    public StatementBlock getBody() {
        return body;
    }

    /**
     * Get parameter declaration.
     *
     * @return the parameter declaration.
     */
    public @Nullable ParameterDeclaration getParameterDeclaration() {
        return parameter;
    }

    /**
     * Get non-standard parameter declaration.
     *
     * @return the parameter declaration.
     */
    public @Nullable CcatchNonstandardParameterDeclaration getNonStdParameterDeclaration() {
        return nonStdParameter;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatch(this);
    }
}
