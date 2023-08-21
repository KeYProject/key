/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;

/**
 * Array length reference. As a length reference is int-valued, and hence it is no valid prefix.
 *
 * @author AL
 */

public class ArrayLengthReference extends JavaNonTerminalProgramElement
        implements Reference, Expression, ReferenceSuffix {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1267866126524827730L;

    /**
     * Expression parent.
     */

    protected ExpressionContainer expressionParent;

    /**
     * Reference prefix. It must evaluate to an ArrayType.
     */

    protected ReferencePrefix prefix;

    /**
     * Array length reference.
     */

    public ArrayLengthReference() {
        super();
    }

    /**
     * Array length reference.
     */

    public ArrayLengthReference(ReferencePrefix prefix) {
        setReferencePrefix(prefix);
        makeParentRoleValid();
    }

    /**
     * Array length reference.
     *
     * @param proto an array length reference.
     */

    protected ArrayLengthReference(ArrayLengthReference proto) {
        super(proto);
        if (proto.prefix != null) {
            prefix = (ReferencePrefix) proto.prefix.deepClone();
        }
        makeParentRoleValid();

    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ArrayLengthReference deepClone() {
        return new ArrayLengthReference(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (prefix != null) {
            prefix.setReferenceSuffix(this);
        }
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        return expressionParent;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        return (prefix != null) ? 1 : 0;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException if <tt>index</tt> is out of bounds
     */

    public ProgramElement getChildAt(int index) {
        if (prefix != null && index == 0) {
            return prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        if (prefix == child) {
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
     * @throws ClassCastException if the new child cannot take over the role of the old one.
     */

    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (prefix == p) {
            ReferencePrefix r = (ReferencePrefix) q;
            prefix = r;
            if (r != null) {
                r.setReferenceSuffix(this);
            }
            return true;
        }
        return false;
    }

    /**
     * Get reference prefix.
     *
     * @return the reference prefix.
     */

    public ReferencePrefix getReferencePrefix() {
        return prefix;
    }

    /**
     * Set reference prefix.
     *
     * @param prefix a reference prefix.
     */

    public void setReferencePrefix(ReferencePrefix prefix) {
        this.prefix = prefix;
    }

    /**
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        return expressionParent;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */

    public void setExpressionContainer(ExpressionContainer c) {
        expressionParent = c;
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? this : prefix.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitArrayLengthReference(this);
    }
}
