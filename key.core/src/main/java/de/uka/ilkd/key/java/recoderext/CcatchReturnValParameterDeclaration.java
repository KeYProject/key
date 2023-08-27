/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.java.ParameterContainer;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.declaration.ParameterDeclaration;

/**
 * A "\Return" parameter of a ccatch clause.
 *
 * @author Dominic Steinhöfel
 */
public class CcatchReturnValParameterDeclaration extends CcatchNonstandardParameterDeclaration
        implements ParameterContainer {
    private static final long serialVersionUID = 1L;

    /**
     * Parent.
     */
    private ParameterContainer parent;

    private ParameterDeclaration delegate;

    public CcatchReturnValParameterDeclaration() {
        // nothing to do here
    }

    public CcatchReturnValParameterDeclaration(ParameterDeclaration delegate) {
        this.delegate = delegate;
        makeParentRoleValid();
    }

    /**
     * Parameter declaration.
     *
     * @param proto a parameter declaration.
     */
    protected CcatchReturnValParameterDeclaration(CcatchReturnValParameterDeclaration proto) {
        delegate = proto.delegate;
        makeParentRoleValid();
    }

    public ParameterDeclaration getDelegate() {
        return delegate;
    }

    public void setDelegate(ParameterDeclaration delegate) {
        this.delegate = delegate;
    }

    /**
     * Make parent role valid.
     */
    @Override
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (delegate != null) {
            delegate.makeParentRoleValid();
            delegate.setParameterContainer(this);
        }
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */
    @Override
    public ParameterContainer getASTParent() {
        return parent;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    @Override
    public int getChildCount() {
        return delegate == null ? 0 : 1;
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
    public int getChildPositionCode(ProgramElement child) {
        if (child == delegate) {
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
     * @exception ClassCastException if the new child cannot take over the role of the old one.
     */
    @Override
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (delegate == p) {
            setDelegate((ParameterDeclaration) q);
            return true;
        }
        return false;
    }

    /**
     * Get parameter container.
     *
     * @return the parameter container.
     */
    @Override
    public ParameterContainer getParameterContainer() {
        return parent;
    }

    /**
     * Set parameter container.
     *
     * @param c a parameter container.
     */
    @Override
    public void setParameterContainer(ParameterContainer c) {
        parent = c;
    }

    @Override
    public CcatchReturnValParameterDeclaration deepClone() {
        if (delegate != null) {
            return new CcatchReturnValParameterDeclaration(delegate.deepClone());
        } else {
            return new CcatchReturnValParameterDeclaration();
        }
    }

    @Override
    public void accept(SourceVisitor v) {
        if (v instanceof SourceVisitorExtended) {
            ((SourceVisitorExtended) v).visitCcatchReturnValParameterDeclaration(this);
        } else {
            // throw new IllegalStateException(
            // "Method 'accept' not implemented in Ccatch");
        }
    }

    @Override
    public Statement getStatementAt(int arg0) {
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getStatementCount() {
        return 0;
    }

    @Override
    public ParameterDeclaration getParameterDeclarationAt(int idx) {
        if (delegate != null && idx == 0) {
            return delegate;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public int getParameterDeclarationCount() {
        return delegate != null ? 1 : 0;
    }
}
