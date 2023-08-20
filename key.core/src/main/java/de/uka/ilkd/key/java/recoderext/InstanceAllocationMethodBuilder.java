/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.ParameterDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.Static;
import recoder.java.reference.TypeReference;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class InstanceAllocationMethodBuilder extends RecoderModelTransformer {

    public static final String IMPLICIT_INSTANCE_ALLOCATE = "<allocate>";

    public InstanceAllocationMethodBuilder(CrossReferenceServiceConfiguration services,
            TransformerCache cache) {
        super(services, cache);
    }


    /**
     * creates a method declaration with no implementation. The methods intention is to allocate a
     * new object of the type it is declared in and to return it. The functionality will be
     * described using taclets
     */
    private MethodDeclaration createAllocateMethod(ClassDeclaration type) {
        ASTList<DeclarationSpecifier> modifiers = new ASTArrayList<>(2);
        modifiers.add(new Public());
        modifiers.add(new Static());

        ASTArrayList<ParameterDeclaration> pdal = new ASTArrayList<>(1);

        MethodDeclaration md = new MethodDeclaration(modifiers, new TypeReference(getId(type)),
            new ImplicitIdentifier(IMPLICIT_INSTANCE_ALLOCATE), pdal, null, null);
        md.makeAllParentRolesValid();
        return md;
    }


    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof ClassDeclaration) {
            attach(createAllocateMethod((ClassDeclaration) td), td, td.getMembers().size());
        }
    }

}
