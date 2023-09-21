/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import java.util.Optional;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Ccatch.
 *
 */
public class Ccatch extends BranchImp implements ParameterContainer, VariableScope {

    /**
     * Parameter.
     */
    protected final Optional<ParameterDeclaration> parameter;

    private Optional<CcatchNonstandardParameterDeclaration> nonStdParameter;

    /**
     * Body.
     */
    protected final StatementBlock body;

    /**
     * Ccatch.
     */
    public Ccatch() {
        super();
        parameter = Optional.empty();
        body = null;
    }

    /**
     * Ccatch.
     *
     * @param e a parameter declaration.
     * @param body a statement.
     */
    public Ccatch(ParameterDeclaration e, StatementBlock body) {
        super();
        this.body = body;
        parameter = Optional.of(e);
        nonStdParameter = Optional.empty();
    }

    /**
     * Ccatch.
     *
     * @param e a parameter declaration.
     * @param body a statement.
     */
    public Ccatch(CcatchNonstandardParameterDeclaration e, StatementBlock body) {
        super();
        this.body = body;
        parameter = Optional.empty();
        nonStdParameter = Optional.of(e);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     *
     * @param children the children of this AST element as KeY classes. May contain: Comments, a
     *        ParameterDeclaration (declaring the catched exceptions) a StatementBlock (as the
     *        action to do when catching)
     */
    public Ccatch(ExtList children) {
        super(children);
        parameter = Optional.ofNullable(children.get(ParameterDeclaration.class));
        nonStdParameter =
            Optional.ofNullable(children.get(CcatchNonstandardParameterDeclaration.class));
        body = children.get(StatementBlock.class);
    }

    @Override
    public SourceElement getLastElement() {
        return (body != null) ? body.getLastElement() : this;
    }

    public boolean hasParameterDeclaration() {
        return parameter.isPresent();
    }

    public boolean hasNonStdParameterDeclaration() {
        return nonStdParameter.isPresent();
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
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */
    @Override
    public ProgramElement getChildAt(int index) {
        if (hasParameterDeclaration()) {
            if (index == 0) {
                return parameter.get();
            }
            index--;
        }
        if (hasNonStdParameterDeclaration()) {
            if (index == 0) {
                return nonStdParameter.get();
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
     * @param index an index for a parameter declaration.
     *
     * @return the parameter declaration with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    @Override
    public ParameterDeclaration getParameterDeclarationAt(int index) {
        if (hasParameterDeclaration() && index == 0) {
            return parameter.get();
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Return the non-standard parameter declaration at the specified index in this node's "virtual"
     * parameter declaration array.
     *
     * @param index an index for a parameter declaration.
     *
     * @return the parameter declaration with the given index.
     *
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds.
     */
    public CcatchNonstandardParameterDeclaration getNonStdParameterDeclarationAt(int index) {
        if (hasNonStdParameterDeclaration() && index == 0) {
            return nonStdParameter.get();
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
    public ParameterDeclaration getParameterDeclaration() {
        return parameter.orElse(null);
    }

    /**
     * Get non-standard parameter declaration.
     *
     * @return the parameter declaration.
     */
    public CcatchNonstandardParameterDeclaration getNonStdParameterDeclaration() {
        return nonStdParameter.orElse(null);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatch(this);
    }
}
