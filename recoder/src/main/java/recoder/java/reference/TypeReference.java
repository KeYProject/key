/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.list.generic.ASTList;

/**
 * TypeReferences reference {@link recoder.abstraction.Type}s by name. A TypeReference can refer to
 * an outer or inner type and hence can also be a {@link MemberReference}, but does not have to. A
 * TypeReference can also occur as part of a reference path and as a prefix for types, too. As a
 * possible suffix for types, it can have other TypeReferences as a prefix, playing the role of a
 * {@link TypeReferenceContainer}.
 */

public class TypeReference extends JavaNonTerminalProgramElement implements TypeReferenceInfix,
        TypeReferenceContainer, PackageReferenceContainer, MemberReference {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -8415845940952618808L;

    /**
     * Parent.
     */

    protected TypeReferenceContainer parent;

    /**
     * Prefix.
     */

    protected ReferencePrefix prefix;

    /**
     * Dimensions.
     */
    protected int dimensions;

    /**
     * Type Arguments
     */
    protected ASTList<TypeArgumentDeclaration> typeArguments;

    /**
     * Name.
     */

    protected Identifier name;

    /**
     * Type reference.
     */

    public TypeReference() {
        // nothing to do here
    }

    /**
     * Type reference.
     *
     * @param name an identifier.
     */

    public TypeReference(Identifier name) {
        setIdentifier(name);
        makeParentRoleValid();
    }

    /**
     * Type reference.
     *
     * @param prefix a reference prefix.
     * @param name an identifier.
     */

    public TypeReference(ReferencePrefix prefix, Identifier name) {
        setIdentifier(name);
        setReferencePrefix(prefix);
        makeParentRoleValid();
    }

    /**
     * Type reference.
     *
     * @param name an identifier.
     * @param dim an int value.
     */

    public TypeReference(Identifier name, int dim) {
        setIdentifier(name);
        setDimensions(dim);
        makeParentRoleValid();
    }

    public TypeReference(Identifier name, ASTList<TypeArgumentDeclaration> typeArgs) {
        setIdentifier(name);
        this.typeArguments = typeArgs;
        makeParentRoleValid();
    }

    /**
     * Type reference.
     *
     * @param proto a type reference.
     */

    protected TypeReference(TypeReference proto) {
        super(proto);
        if (proto.prefix != null) {
            prefix = (ReferencePrefix) proto.prefix.deepClone();
        }
        if (proto.name != null) {
            name = proto.name.deepClone();
        }
        if (proto.typeArguments != null) {
            typeArguments = proto.typeArguments.deepClone();
        }
        dimensions = proto.dimensions;
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public TypeReference deepClone() {
        return new TypeReference(this);
    }

    /**
     * Make parent role valid.
     */

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (prefix != null) {
            prefix.setReferenceSuffix(this);
        }
        if (name != null) {
            name.setParent(this);
        }
        if (typeArguments != null) {
            for (TypeArgumentDeclaration ta : typeArguments) {
                ta.setParent(this);
            }
        }
    }

    public SourceElement getFirstElement() {
        return (prefix == null) ? name : prefix.getFirstElement();
    }

    /**
     * Get AST parent.
     *
     * @return the non terminal program element.
     */

    public NonTerminalProgramElement getASTParent() {
        return parent;
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
        if (typeArguments != null) {
            result += typeArguments.size();
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
            index--;
        }
        if (typeArguments != null) {
            return typeArguments.get(index);
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: prefix
        // role 1: name
        // role 2(idx): type argument
        if (prefix == child) {
            return 0;
        }
        if (name == child) {
            return 1;
        }
        if (typeArguments != null) {
            int idx = typeArguments.indexOf(child);
            if (idx != -1) {
                return (idx << 4) | 2;
            }
        }
        return -1;
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
        if (typeArguments != null) {
            int idx = typeArguments.indexOf(p);
            if (idx != -1) {
                if (q == null) {
                    typeArguments.remove(idx);
                } else {
                    typeArguments.set(idx, (TypeArgumentDeclaration) q);
                    ((TypeArgumentDeclaration) q).setParent(this);
                }
                return true;
            }
        }
        return false;
    }

    /**
     * Get parent.
     *
     * @return the type reference container.
     */

    public TypeReferenceContainer getParent() {
        return parent;
    }

    /**
     * Set parent.
     *
     * @param elem a type reference container.
     */

    public void setParent(TypeReferenceContainer elem) {
        parent = elem;
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
     * @param x a reference prefix.
     */

    public void setReferencePrefix(ReferencePrefix x) {
        prefix = x;
    }

    /**
     * Get the package reference.
     *
     * @return the package reference.
     */

    public PackageReference getPackageReference() {
        return (prefix instanceof PackageReference) ? (PackageReference) prefix : null;
    }

    /**
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return (parent instanceof ReferenceSuffix) ? (ReferenceSuffix) parent : null;
    }

    /**
     * Set reference suffix.
     *
     * @param x a reference suffix, must also be a type reference container.
     */

    public void setReferenceSuffix(ReferenceSuffix x) {
        parent = (TypeReferenceContainer) x;
    }

    /**
     * Get dimensions.
     *
     * @return the int value.
     */

    public int getDimensions() {
        return dimensions;
    }

    /**
     * Set dimensions.
     *
     * @param dim an int value.
     */

    public void setDimensions(int dim) {
        dimensions = dim;
    }

    /**
     * Get name.
     *
     * @return the string.
     */

    public final String getName() {
        return (name == null) ? null : name.getText();
    }

    /**
     * Get identifier.
     *
     * @return the identifier.
     */

    public Identifier getIdentifier() {
        return name;
    }

    /**
     * Set identifier.
     *
     * @param id an identifier.
     */

    public void setIdentifier(Identifier id) {
        name = id;
    }

    public void accept(SourceVisitor v) {
        v.visitTypeReference(this);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return typeArguments;
    }

    public void setTypeArguments(ASTList<TypeArgumentDeclaration> ta) {
        this.typeArguments = ta;
    }

}
