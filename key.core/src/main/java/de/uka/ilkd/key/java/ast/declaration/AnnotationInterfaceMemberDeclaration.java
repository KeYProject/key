/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.declaration;

import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;

import org.key_project.util.collection.ImmutableArray;

public class AnnotationInterfaceMemberDeclaration extends JavaDeclaration
        implements MemberDeclaration {
    private final TypeReference typeRef;

    private final ProgramElementName name;

    public AnnotationInterfaceMemberDeclaration(TypeReference typeRef, ProgramElementName name,
            ImmutableArray<Modifier> modifiers) {
        super(modifiers);

        this.typeRef = typeRef;
        this.name = name;
    }

    @Override
    public int getChildCount() {
        int result = 0;

        if (modArray != null)
            result += modArray.size();
        if (name != null)
            result++;
        if (typeRef != null)
            result++;

        return result;
    }

    @Override
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
        if (typeRef != null) {
            if (index == 0)
                return typeRef;
            index--;
        }
        throw new ArrayIndexOutOfBoundsException();
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAnnotationInterfaceMemberDeclaration(this);
    }

    public TypeReference getTypeRef() {
        return typeRef;
    }

    public ProgramElementName getProgramElementName() {
        return name;
    }

    public boolean isPrivate() { return false; }

    public boolean isProtected() { return false; }

    public boolean isPublic() { return true; }

    public boolean isStatic() { return false; }

    public boolean isStrictFp() { return false; }
}
