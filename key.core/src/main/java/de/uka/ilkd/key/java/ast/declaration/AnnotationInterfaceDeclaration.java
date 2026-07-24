/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;


public class AnnotationInterfaceDeclaration extends TypeDeclaration {
    public AnnotationInterfaceDeclaration(
            PositionInfo pi, List<Comment> comments,
            @NonNull ImmutableArray<Modifier> modArray,
            ProgramElementName name, ProgramElementName fullName,
            ImmutableArray<MemberDeclaration> members, boolean parentIsInterfaceDeclaration,
            boolean isLibrary, List<TextualJMLConstruct> jmlAttachments) {
        super(pi, comments, modArray, name, fullName, members, parentIsInterfaceDeclaration,
            isLibrary, ImmutableList.fromList(jmlAttachments));
    }

    /**
     * returns the local declared supertypes
     */
    public ImmutableList<KeYJavaType> getSupertypes() {
        return ImmutableList.of();
    }

    /**
     * calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnAnnotationInterfaceDeclaration(this);
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
        if (members != null)
            result += members.size();
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
        int len;
        if (modArray != null) {
            len = modArray.size();
            if (len > index)
                return modArray.get(index);
            index -= len;
        }
        if (name != null) {
            if (index == 0)
                return name;
            index--;
        }
        if (members != null)
            return members.get(index);
        throw new ArrayIndexOutOfBoundsException();
    }

    public boolean isInterface() {
        return true;
    }
}
