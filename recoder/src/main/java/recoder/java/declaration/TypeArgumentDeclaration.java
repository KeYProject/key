/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.abstraction.TypeArgument;
import recoder.convenience.Naming;
import recoder.java.*;
import recoder.java.reference.MethodReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.TypeReferenceContainer;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.list.generic.ASTList;

/**
 * This class represents a TypeArgument, as e.g. given in variable declarations.
 *
 * @author Tobias Gutzmann
 */
public class TypeArgumentDeclaration extends JavaNonTerminalProgramElement
        implements TypeReferenceContainer, TypeArgument {
    /**
     * serialization id
     */
    private static final long serialVersionUID = -8369885569636132718L;

    protected TypeReference typeReference;

    // the wildcard mode
    protected WildcardMode wildcardMode;

    // either a TypeReference, a URQ, or a MethodReference
    protected Reference parent;

    /**
     *
     */
    public TypeArgumentDeclaration() {
        this(null, WildcardMode.Any);
    }

    /**
     * @param proto
     */
    protected TypeArgumentDeclaration(TypeArgumentDeclaration proto) {
        super(proto);
        this.wildcardMode = proto.wildcardMode;
        if (proto.typeReference != null) {
            this.typeReference = proto.typeReference.deepClone();
        }
        makeParentRoleValid();
    }

    public TypeArgumentDeclaration(TypeReference tr) {
        this(tr, WildcardMode.None);
    }

    public TypeArgumentDeclaration(TypeReference tr, WildcardMode wm) {
        this.typeReference = tr;
        this.wildcardMode = wm;
        makeParentRoleValid();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.reference.TypeReferenceContainer#getTypeReferenceCount()
     */
    public int getTypeReferenceCount() {
        return typeReference == null ? 0 : 1;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.reference.TypeReferenceContainer#getTypeReferenceAt(int)
     */
    public TypeReference getTypeReferenceAt(int index) {
        if (index == 0 && typeReference != null) {
            return typeReference;
        }
        throw new ArrayIndexOutOfBoundsException(index);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildCount()
     */
    public int getChildCount() {
        return getTypeReferenceCount();
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildAt(int)
     */
    public ProgramElement getChildAt(int index) {
        return getTypeReferenceAt(index);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#getChildPositionCode(recoder.java.ProgramElement)
     */
    public int getChildPositionCode(ProgramElement child) {
        // 0: typeReference
        if (child == typeReference) {
            return 0;
        }
        return -1;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.NonTerminalProgramElement#replaceChild(recoder.java.ProgramElement,
     * recoder.java.ProgramElement)
     */
    public boolean replaceChild(ProgramElement p, ProgramElement q) {
        if (p == null) {
            throw new NullPointerException();
        }
        if (p == typeReference) {
            typeReference = (TypeReference) q;
            if (typeReference != null) {
                typeReference.setParent(this);
            }
            return true;
        }
        return false;
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.ProgramElement#getASTParent()
     */
    public NonTerminalProgramElement getASTParent() {
        return (NonTerminalProgramElement) parent;
    }

    public Reference getParent() {
        return parent;
    }

    /**
     * @param tr either a TypeReference, a URQ, or an MethodReference
     * @throws IllegalArgumentException if <code>tr</code> isn't of type TypeReference, URQ, or
     *         MethodReference
     */
    public void setParent(Reference tr) {
        parent = tr;
        if (!(tr instanceof TypeReference || tr instanceof UncollatedReferenceQualifier
                || tr instanceof MethodReference)) {
            throw new IllegalArgumentException();
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#accept(recoder.java.SourceVisitor)
     */
    public void accept(SourceVisitor v) {
        v.visitTypeArgument(this);
    }

    /*
     * (non-Javadoc)
     *
     * @see recoder.java.SourceElement#deepClone()
     */
    public TypeArgumentDeclaration deepClone() {
        return new TypeArgumentDeclaration(this);
    }

    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (typeReference != null) {
            typeReference.setParent(this);
        }
    }

    public WildcardMode getWildcardMode() {
        return wildcardMode;
    }

    public void setWildcardMode(WildcardMode wm) {
        this.wildcardMode = wm;
    }

    public String getTypeName() {
        return Naming.toPathName(typeReference);
    }

    /**
     * Returns type reference's type arguments, or null if wildcardMode == WildcardMode.Any
     */
    public ASTList<TypeArgumentDeclaration> getTypeArguments() {
        if (wildcardMode == WildcardMode.Any) {
            return null;
        }
        // otherwise, type reference must be set. Leave at it is for now for error detection
        return typeReference.getTypeArguments();
    }

    public TypeReference getTypeReference() {
        return typeReference;
    }

    public void setTypeReference(TypeReference tr) {
        this.typeReference = tr;
    }

    @Override
    public SourceElement getFirstElement() {
        if (wildcardMode != WildcardMode.None) {
            return this;
        }
        return typeReference == null ? this : typeReference.getFirstElement();
    }

}
