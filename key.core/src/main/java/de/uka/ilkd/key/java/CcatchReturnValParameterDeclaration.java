/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * A "\Return int v" parameter declaration of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchReturnValParameterDeclaration extends CcatchNonstandardParameterDeclaration
        implements ParameterContainer {

    private final ParameterDeclaration delegate;

    public CcatchReturnValParameterDeclaration(ExtList children) {
        delegate = children.get(ParameterDeclaration.class);
    }

    public ParameterDeclaration getDelegate() {
        return delegate;
    }

    public VariableSpecification getVariableSpecification() {
        return delegate.getVariableSpecification();
    }

    public ImmutableArray<VariableSpecification> getVariables() {
        return delegate.getVariables();
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        return delegate != null ? 1 : 0;
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
        if (delegate != null && index == 0) {
            return delegate;
        }

        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnCcatchReturnValParameterDeclaration(this);
    }

    @Override
    public int getStatementCount() {
        return 0;
    }

    @Override
    public Statement getStatementAt(int index) {
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getParameterDeclarationCount() {
        return delegate != null ? 1 : 0;
    }

    @Override
    public ParameterDeclaration getParameterDeclarationAt(int idx) {
        if (delegate != null && idx == 0) {
            return delegate;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        return super.match(source, matchCond);
    }

}
