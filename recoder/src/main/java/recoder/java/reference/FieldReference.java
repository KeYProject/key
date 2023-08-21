/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;

/**
 * Field reference.
 *
 * @author <TT>AutoDoc</TT>
 */

public class FieldReference extends VariableReference
        implements MemberReference, ReferenceSuffix, TypeReferenceContainer, ExpressionContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1475141413582182288L;

    /**
     * Reference prefix.
     */

    protected ReferencePrefix prefix;

    /**
     * Field reference.
     */

    public FieldReference() {
        // nothing to do
    }

    /**
     * Field reference.
     *
     * @param id an identifier.
     */

    public FieldReference(Identifier id) {
        super(id);
    }

    /**
     * Field reference.
     *
     * @param prefix a reference prefix.
     * @param id an identifier.
     */

    public FieldReference(ReferencePrefix prefix, Identifier id) {
        super(id);
        setReferencePrefix(prefix);
        makeParentRoleValid(); // neccessary for prefix
    }

    /**
     * Field reference.
     *
     * @param proto a field reference.
     */

    protected FieldReference(FieldReference proto) {
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

    public FieldReference deepClone() {
        return new FieldReference(this);
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
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int result = 0;
        if (prefix != null) {
            result++;
        }
        if (name != null) {
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
        if (prefix != null) {
            if (index == 0) {
                return prefix;
            }
            index--;
        }
        if (name != null) {
            if (index == 0) {
                return name;
            }
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        // role 1: name
        if (prefix == child) {
            return 0;
        }
        if (name == child) {
            return 1;
        }
        return -1;
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
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */

    public int getTypeReferenceCount() {
        return (prefix instanceof TypeReference) ? 1 : 0;
    }

    /*
     * Return the type reference at the specified index in this node's "virtual" type reference
     * array. @param index an index for a type reference. @return the type reference with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public TypeReference getTypeReferenceAt(int index) {
        if (prefix instanceof TypeReference && index == 0) {
            return (TypeReference) prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get the number of expressions in this container.
     *
     * @return the number of expressions.
     */

    public int getExpressionCount() {
        return (prefix instanceof Expression) ? 1 : 0;
    }

    /*
     * Return the expression at the specified index in this node's "virtual" expression
     * array. @param index an index for an expression. @return the expression with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */

    public Expression getExpressionAt(int index) {
        if (prefix instanceof Expression && index == 0) {
            return (Expression) prefix;
        }
        throw new ArrayIndexOutOfBoundsException();
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
        if (name == p) {
            Identifier r = (Identifier) q;
            name = r;
            if (r != null) {
                r.setParent(this);
            }
            return true;
        }
        return false;
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? name : prefix.getFirstElement();
    }

    public void accept(SourceVisitor v) {
        v.visitFieldReference(this);
    }
}
