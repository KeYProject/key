/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.declaration;

import recoder.ModelException;
import recoder.abstraction.AnnotationUse;
import recoder.java.NonTerminalProgramElement;
import recoder.java.SourceVisitor;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/**
 * @author Tobias Gutzmann
 */
public class EnumConstantDeclaration extends FieldDeclaration implements MemberDeclaration {
    /**
     * serialization id
     */
    private static final long serialVersionUID = 6254325025698455465L;

    /**
     *
     */
    public EnumConstantDeclaration() {
        super();
    }

    public EnumConstantDeclaration(EnumConstantSpecification spec,
            ASTList<DeclarationSpecifier> annotations) {
        super();
        setEnumConstantSpecification(spec);
        setDeclarationSpecifiers(annotations);
        makeParentRoleValid();
    }

    /**
     * @param proto
     */
    protected EnumConstantDeclaration(EnumConstantDeclaration proto) {
        super(proto);
        makeParentRoleValid();
    }

    public EnumDeclaration getParent() {
        return (EnumDeclaration) parent;
    }

    @Override
    public void accept(SourceVisitor v) {
        v.visitEnumConstantDeclaration(this);
    }

    @Override
    public boolean isFinal() {
        // implicitly
        return true;
    }

    @Override
    public boolean isStatic() {
        // implicitly
        return true;
    }

    @Override
    public boolean isPrivate() {
        return false;
    }

    @Override
    public boolean isProtected() {
        return false;
    }

    @Override
    public boolean isPublic() {
        // implicitly
        return true;
    }

    @Override
    public boolean isStrictFp() {
        return false;
    }

    @Override
    public NonTerminalProgramElement getASTParent() {
        return parent;
    }

    @Override
    public EnumConstantDeclaration deepClone() {
        return new EnumConstantDeclaration(this);
    }

    public EnumConstantSpecification getEnumConstantSpecification() {
        if (fieldSpecs == null || fieldSpecs.size() == 0) {
            return null;
        }
        return (EnumConstantSpecification) fieldSpecs.get(0);
    }

    /**
     * @param spec
     */
    public void setEnumConstantSpecification(EnumConstantSpecification spec) {
        if (fieldSpecs == null) {
            fieldSpecs = new ASTArrayList<>(1);
        }
        fieldSpecs.add(spec);
    }

    @Override
    public TypeDeclaration getMemberParent() {
        return parent;
    }

    @Override
    public void setMemberParent(TypeDeclaration t) {
        if (!(t instanceof EnumDeclaration)) {
            throw new IllegalArgumentException(
                "Only an EnumDeclarations can be parent of an EnumConstantDeclaration");
        }
        super.setMemberParent(t);
    }

    @Override
    public void validate() throws ModelException {
        if (typeReference != null) {
            throw new ModelException(
                "TypeReference set in EnumConstantDeclaration in " + parent.getFullName());
        }
        if (declarationSpecifiers != null) {
            for (DeclarationSpecifier ds : declarationSpecifiers) {
                if (!(ds instanceof AnnotationUse)) {
                    throw new ModelException("EnumConstantDeclaration may not contain modifiers in "
                        + parent.getFullName());
                }
            }
        }
        if (!(parent instanceof EnumDeclaration)) {
            throw new ModelException("Illegal parent type (" + parent.getClass().getCanonicalName()
                + " - " + parent.getFullName() + ") for EnumConstantDeclaration");
        }
        if (fieldSpecs.size() != 1) {
            throw new ModelException(
                "Only one EnumConstantSpecification per EnumConstantDeclaration allowed in "
                    + parent.getFullName());
        }
        if (!(fieldSpecs.get(0) instanceof EnumConstantSpecification)) {
            throw new ModelException(
                "child of EnumConstantDeclaration is not an EnumConstantSpecification in "
                    + parent.getFullName());
        }
    }

}
