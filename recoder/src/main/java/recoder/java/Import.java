/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java;

import recoder.java.reference.*;

/**
 * Import.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Import extends JavaNonTerminalProgramElement
        implements TypeReferenceContainer, PackageReferenceContainer {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -722260309045817264L;

    /**
     * Multi import flag.
     */
    protected boolean isMultiImport;

    /**
     * Static import flag (Java 5).
     */
    protected boolean isStaticImport;

    /**
     * Parent.
     */
    protected CompilationUnit parent;

    /**
     * Type reference infix.
     */
    protected TypeReferenceInfix reference;

    /**
     * the identifier used if this is a static import.
     */
    protected Identifier staticIdentifier;

    /**
     * Import.
     */
    public Import() {
        // creates uninitialized import
    }

    /**
     * Creates a non-static (default) Import. Same as <code>new Import(t, multi, false)</code>
     *
     * @param t a type reference.
     * @param multi indicates the wildcard.
     */

    public Import(TypeReference t, boolean multi) {
        setReference(t);
        setMultiImport(multi);
        makeParentRoleValid();
    }

    /**
     * Creates a static Import.
     *
     * @param t
     * @param multi
     * @param isStatic
     */
    public Import(TypeReference t, Identifier id) {
        setReference(t);
        setStaticIdentifier(id);
        setMultiImport(false);
        setStaticImport(true);
        makeParentRoleValid();
    }

    public Import(TypeReference t, boolean multi, boolean isStatic) {
        setReference(t);
        setMultiImport(multi);
        setStaticImport(isStatic);
        makeParentRoleValid();
    }

    /**
     * Import.
     *
     * @param t a package reference.
     */
    public Import(PackageReference t) {
        setReference(t);
        setMultiImport(true);
        setStaticImport(false);
        makeParentRoleValid();
    }

    /**
     * Import.
     *
     * @param proto an import.
     */
    protected Import(Import proto) {
        super(proto);
        if (proto.reference != null) {
            reference = (TypeReferenceInfix) proto.reference.deepClone();
        }
        if (proto.staticIdentifier != null) {
            staticIdentifier = proto.staticIdentifier.deepClone();
        }
        isMultiImport = proto.isMultiImport;
        isStaticImport = proto.isStaticImport;
        makeParentRoleValid();
    }

    /**
     * Make parent role valid.
     */
    public void makeParentRoleValid() {
        super.makeParentRoleValid();
        if (staticIdentifier != null) {
            staticIdentifier.setParent(this);
        }
        if (reference instanceof TypeReference) {
            ((TypeReference) reference).setParent(this);
        } else if (reference instanceof PackageReference) {
            ((PackageReference) reference).setParent(this);
        } else if (reference instanceof UncollatedReferenceQualifier) {
            ((UncollatedReferenceQualifier) reference).setParent(this);
        } else {
            throw new IllegalStateException("Unknown reference type encountered");
        }
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */
    public Import deepClone() {
        return new Import(this);
    }

    public SourceElement getLastElement() {
        return reference.getLastElement();
    }

    /**
     * Checks if this import is a multi type import, also known as type-on-demand import.
     *
     * @return the kind of this import.
     */
    public boolean isMultiImport() {
        return isMultiImport;
    }

    /**
     * Sets this import to be a multi type import.
     *
     * @param multi denotes the wildcard for this import.
     * @throws IllegalArgumentException if the reference is a package and multi is <CODE>false
     *                                  </CODE>.
     */
    public void setMultiImport(boolean multi) {
        if (!multi && reference instanceof PackageReference) {
            throw new IllegalArgumentException("Package imports are always multi");
        }
        isMultiImport = multi;
    }

    /**
     * Checks if this import is a static import (Java 5).
     *
     * @return wether or not the import is a static import
     */
    public boolean isStaticImport() {
        return isStaticImport;
    }

    public void setStaticImport(boolean isStatic) {
        isStaticImport = isStatic;
    }

    public Identifier getStaticIdentifier() {
        return staticIdentifier;
    }

    public void setStaticIdentifier(Identifier id) {
        staticIdentifier = id;
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
        if (reference != null) {
            result++;
        }
        if (staticIdentifier != null) {
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
        if (reference != null) {
            if (index == 0) {
                return reference;
            }
            index--;
        }
        if (index == 0 && staticIdentifier != null) {
            return staticIdentifier;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    public int getChildPositionCode(ProgramElement child) {
        // role 0: reference
        // role 1: static identifier (java 5 only)
        if (child == reference) {
            return 0;
        }
        if (child == staticIdentifier) {
            return 1;
        }
        return -1;
    }

    /**
     * Get parent.
     *
     * @return the compilation unit.
     */
    public CompilationUnit getParent() {
        return parent;
    }

    /**
     * Set parent.
     *
     * @param u a compilation unit.
     */
    public void setParent(CompilationUnit u) {
        parent = u;
    }

    /**
     * Get the number of type references in this container.
     *
     * @return the number of type references.
     */
    public int getTypeReferenceCount() {
        return (reference instanceof TypeReference) ? 1 : 0;
    }

    /*
     * Return the type reference at the specified index in this node's "virtual" type reference
     * array. @param index an index for a type reference. @return the type reference with the given
     * index. @exception ArrayIndexOutOfBoundsException if <tt> index </tt> is out of bounds.
     */
    public TypeReference getTypeReferenceAt(int index) {
        if (reference instanceof TypeReference && index == 0) {
            return (TypeReference) reference;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Returns the type reference of this import, if there is one.
     *
     * @return the reference of this import statement.
     */
    public TypeReference getTypeReference() {
        return (reference instanceof TypeReference) ? (TypeReference) reference : null;
    }

    /**
     * Returns the package reference of this import, if there is one. Note that if reference is a
     * URQ, this method will return <code>null</code>, although this URQ may denote a Package.
     *
     * @return the reference of this import statement.
     */
    public PackageReference getPackageReference() {
        return (reference instanceof PackageReference) ? (PackageReference) reference : null;
    }

    /**
     * Returns the reference of this import, either a type or a package reference.
     *
     * @return the reference of this import statement.
     */
    public TypeReferenceInfix getReference() {
        return reference;
    }

    /**
     * Set reference.
     *
     * @param t a type reference infix.
     */
    public void setReference(TypeReferenceInfix t) {
        reference = t;
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
        if (reference == p) {
            TypeReferenceInfix r = (TypeReferenceInfix) q;
            reference = r;
            if (r instanceof TypeReference) {
                ((TypeReference) r).setParent(this);
            } else if (r instanceof PackageReference) {
                ((PackageReference) r).setParent(this);
                isMultiImport = true;
            }
            return true;
        }
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitImport(this);
    }
}
