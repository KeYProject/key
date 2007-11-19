package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Identifier;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.Static;
import recoder.java.reference.TypeReference;
import recoder.list.*;

public class AreaAllocationMethodBuilder extends RecoderModelTransformer {

    public static final String IMPLICIT_AREA_ALLOCATE = "<allocateArea>";


    public AreaAllocationMethodBuilder(CrossReferenceServiceConfiguration services, 
            CompilationUnitMutableList units) {
        super(services, units);      
    }
    
    /**
     * creates a method declaration with no implementation. The methods intention is
     * to allocate a new memory area. The functionality will be described using taclets
     */
    private MethodDeclaration createAllocateMethod(ClassDeclaration type) {
        ModifierMutableList modifiers = new ModifierArrayList(2);
        modifiers.add(new Public());
        modifiers.add(new Static());    
        
        ParameterDeclarationArrayList pdal = new ParameterDeclarationArrayList(1);
        
//        services.getCrossReferenceSourceInfo().getType("long", type);
        pdal.add(new ParameterDeclaration(new TypeReference(new Identifier("long")),
                new Identifier("size")));
        MethodDeclaration md =  new MethodDeclaration
            (modifiers, null,
//             new TypeReference
//             ((Identifier)type.getIdentifier().deepClone()), 
             new ImplicitIdentifier(IMPLICIT_AREA_ALLOCATE), 
             pdal, 
             null, null);
        md.makeAllParentRolesValid();
        return md;
    }


    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof ClassDeclaration) {
            attach(createAllocateMethod((ClassDeclaration)td), td, 
                    td.getMembers().size());
        }

    }
    
}
