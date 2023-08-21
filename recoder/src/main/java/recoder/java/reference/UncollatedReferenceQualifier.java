/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.reference;

import recoder.java.*;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.list.generic.ASTList;

/**
 * This class represents a currently uncollated program element. As it is currently not known which
 * exact program element this reference represents, this class inherits from many different program
 * elements, where inheritance means "may be one of these" instead of "is a".
 *
 * @author AL
 * @author RN
 */

public class UncollatedReferenceQualifier extends JavaNonTerminalProgramElement
        implements TypeReferenceInfix, ExpressionContainer, TypeReferenceContainer,
        PackageReferenceContainer, Reference, Expression {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1896030875000030810L;

    /**
     * Parent. Can be an expression container, or import.
     */

    protected NonTerminalProgramElement parent;

    /**
     * Non-suffix container.
     */
    protected ReferenceSuffix suffix;

    /**
     * Prefix.
     */
    protected ReferencePrefix prefix;

    /**
     * Type Arguments
     */
    protected ASTList<TypeArgumentDeclaration> typeArguments;

    /**
     * Name.
     */

    protected Identifier name;

    /**
     * Uncollated reference qualifier.
     */

    public UncollatedReferenceQualifier() {
        // nothing to do here
    }

    /**
     * Uncollated reference qualifier.
     *
     * @param id an identifier.
     */

    public UncollatedReferenceQualifier(Identifier id) {
        setIdentifier(id);
        makeParentRoleValid();
    }

    /**
     * Uncollated reference qualifier.
     *
     * @param prefix a reference prefix.
     * @param id an identifier.
     */

    public UncollatedReferenceQualifier(ReferencePrefix prefix, Identifier id) {
        setIdentifier(id);
        setReferencePrefix(prefix);
        makeParentRoleValid();
    }

    /**
     * Uncollated reference qualifier.
     *
     * @param proto an uncollated reference qualifier.
     */

    protected UncollatedReferenceQualifier(UncollatedReferenceQualifier proto) {
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
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public UncollatedReferenceQualifier deepClone() {
        return new UncollatedReferenceQualifier(this);
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
        return parent != null ? parent : suffix;
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
     * Get expression container.
     *
     * @return the expression container.
     */

    public ExpressionContainer getExpressionContainer() {
        if (parent instanceof ExpressionContainer) {
            return (ExpressionContainer) parent;
        }
        return null;
    }

    /**
     * Set expression container.
     *
     * @param c an expression container.
     */

    public void setExpressionContainer(ExpressionContainer c) {
        parent = c;
        suffix = null;
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
     * Get the package reference.
     *
     * @return the package reference.
     */

    public PackageReference getPackageReference() {
        return (prefix instanceof PackageReference) ? (PackageReference) prefix : null;
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
     * Get reference suffix.
     *
     * @return the reference suffix.
     */

    public ReferenceSuffix getReferenceSuffix() {
        return suffix;
    }

    /**
     * Set reference suffix.
     *
     * @param x a reference suffix.
     */

    public void setReferenceSuffix(ReferenceSuffix x) {
        suffix = x;
        parent = null;
    }

    /**
     * Sets an import statement as parent. Useful for Java 5 only, where Identifiers are part of
     * static imports.
     *
     * @param imp an import statement.
     */

    public void setParent(Import imp) {
        parent = imp;
        suffix = null;
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

    private void copySourceInfos(Reference ref) {
        ref.setRelativePosition(getRelativePosition());
        ref.setStartPosition(getStartPosition());
        ref.setEndPosition(getEndPosition());
        ref.setComments(comments);
    }

    /**
     * To array length reference.
     *
     * @return the array length reference.
     */

    public ArrayLengthReference toArrayLengthReference() {
        ArrayLengthReference ref = getFactory().createArrayLengthReference();
        ref.setExpressionContainer(getExpressionContainer());
        ref.setReferencePrefix(prefix);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    /**
     * To variable reference.
     *
     * @return the variable reference.
     */

    public VariableReference toVariableReference() {
        VariableReference ref = getFactory().createVariableReference();
        ref.setExpressionContainer(getExpressionContainer());
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setIdentifier(name);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    /**
     * To field reference.
     *
     * @return the variable reference.
     */

    public VariableReference toFieldReference() {
        FieldReference ref = getFactory().createFieldReference();
        ref.setExpressionContainer(getExpressionContainer());
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setReferencePrefix(prefix);
        ref.setIdentifier(name);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    /**
     * To type reference.
     *
     * @return the type reference.
     */

    public TypeReference toTypeReference() {
        TypeReference ref = getFactory().createTypeReference();
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setReferencePrefix(prefix);
        ref.setIdentifier(name);
        ref.setTypeArguments(typeArguments);
        ref.makeParentRoleValid();
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    /**
     * To package reference. Converts the prefix, if necessary.
     *
     * @return the package reference.
     */

    public PackageReference toPackageReference() {
        if (prefix instanceof UncollatedReferenceQualifier) {
            prefix = ((UncollatedReferenceQualifier) prefix).toPackageReference();
        }
        PackageReference ref = getFactory().createPackageReference();
        ref.setReferenceSuffix(getReferenceSuffix());
        ref.setReferencePrefix(prefix);
        ref.setIdentifier(name);
        copySourceInfos(ref);
        ref.makeParentRoleValid();
        return ref;
    }

    public void accept(SourceVisitor v) {
        v.visitUncollatedReferenceQualifier(this);
    }

    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        return typeArguments;
    }

    public void setTypeArguments(ASTList<TypeArgumentDeclaration> ta) {
        this.typeArguments = ta;
    }
}
