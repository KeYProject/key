/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

/**
 * Interface declaration.
 */
public class InterfaceDeclaration extends TypeDeclaration {
    protected final Extends extending;


    public InterfaceDeclaration(PositionInfo pi, List<Comment> comments,
            @NonNull ImmutableArray<Modifier> modArray, ProgramElementName name,
            ProgramElementName fullName, ImmutableArray<MemberDeclaration> members,
            boolean parentIsInterfaceDeclaration, boolean isLibrary, Extends extending) {
        super(pi, comments, modArray, name, fullName, members, parentIsInterfaceDeclaration,
            isLibrary);
        this.extending = extending;
    }

    public InterfaceDeclaration() {
        extending = null;
    }

    /**
     * Construct a new outer or member interface class.
     */
    public InterfaceDeclaration(Modifier[] modifiers, ProgramElementName name,
            ProgramElementName fullName,
            Extends extended, MemberDeclaration[] members,
            boolean isLibrary) {
        super(modifiers, name, fullName, members, false, isLibrary);
        extending = extended;
    }

    /**
     * Construct a new outer or member interface class.
     */
    public InterfaceDeclaration(Modifier[] modifiers, ProgramElementName name,
            Extends extended, MemberDeclaration[] members,
            boolean isLibrary) {
        this(modifiers, name, name, extended, members, isLibrary);
    }

    /**
     * uses children list to create non-anonymous class
     *
     * @param children
     *        an ExtList that may contain: an Extends
     *        (as pointer to a class), ProgramElementName (as name),
     *        several MemberDeclaration (as members of
     *        the type), a parentIsInterfaceDeclaration (indicating if parent is
     *        interface), several Modifier (as modifiers of the type decl), a Comment
     * @param fullName
     *        the fully qualified ProgramElementName of the declared
     *        type
     * @param isLibrary
     *        a boolean flag indicating if this interface is part of
     *        a library (library interfaces come often with a specification and are
     *        only available as bytecode)
     */
    public InterfaceDeclaration(ExtList children, ProgramElementName fullName,
            boolean isLibrary) {
        super(children, fullName, isLibrary);
        extending = children.get(Extends.class);
    }

    public InterfaceDeclaration(ProgramElementName name) {
        this(new Modifier[] {},
            name, null,
            new MemberDeclaration[] {},
            true);
    }


    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
        int result = 0;
        if (modArray != null)
            result += modArray.size();
        if (name != null)
            result++;
        if (extending != null)
            result++;
        if (members != null)
            result += members.size();
        return result;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @throws ArrayIndexOutOfBoundsException
     *         if <tt>index</tt> is out
     *         of bounds
     */
    public ProgramElement getChildAt(int index) {
        int len;
        if (modArray != null) {
            len = modArray.size();
            if (len > index) {
                return modArray.get(index);
            }
            index -= len;
        }
        if (name != null) {
            if (index == 0)
                return name;
            index--;
        }
        if (extending != null) {
            if (index == 0)
                return extending;
            index--;
        }
        if (members != null) {
            len = members.size();
            if (len > index) {
                return members.get(index);
            }
            index -= len;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    /**
     * Get extended types.
     *
     * @return the extends.
     */
    public Extends getExtendedTypes() {
        return extending;
    }

    /**
     * Interfaces are always abstract.
     */
    public boolean isAbstract() {
        return true;
    }

    /**
     * Interfaces are never native.
     */
    public boolean isNative() {
        return false;
    }

    /**
     * Interfaces are never protected.
     */
    public boolean isProtected() {
        return false;
    }

    /**
     * Interfaces are never private.
     */
    public boolean isPrivate() {
        return false;
    }

    /**
     * Interfaces are never strictfp.
     */

    public boolean isStrictFp() {
        return false;
    }

    /**
     * Interfaces are never synchronized.
     */
    public boolean isSynchronized() {
        return false;
    }

    /**
     * Interfaces are never transient.
     */
    public boolean isTransient() {
        return false;
    }

    /**
     * Interfaces are never volatile.
     */
    public boolean isVolatile() {
        return false;
    }

    public boolean isInterface() {
        return true;
    }

    /**
     * returns the local declared supertypes
     */
    public ImmutableList<KeYJavaType> getSupertypes() {
        ImmutableList<KeYJavaType> types = ImmutableSLList.<KeYJavaType>nil();
        if (extending != null) {
            for (int i = extending.getTypeReferenceCount() - 1; i >= 0; i--) {
                types = types.prepend(extending.getTypeReferenceAt(i).getKeYJavaType());
            }
        }
        return types;
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnInterfaceDeclaration(this);
    }
}
