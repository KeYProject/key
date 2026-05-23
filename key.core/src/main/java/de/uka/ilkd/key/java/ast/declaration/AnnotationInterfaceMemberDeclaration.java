package de.uka.ilkd.key.java.ast.declaration;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.reference.TypeReference;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;

public class AnnotationInterfaceMemberDeclaration extends JavaDeclaration {
    private final TypeReference typeRef;

    private final ProgramElementName name;

    public AnnotationInterfaceMemberDeclaration(TypeReference typeRef, ProgramElementName name, ImmutableArray<Modifier> modifiers) {
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
}
