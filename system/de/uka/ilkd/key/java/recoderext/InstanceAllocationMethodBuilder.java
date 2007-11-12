package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Identifier;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.modifier.Private;
import recoder.java.declaration.modifier.Static;
import recoder.java.reference.TypeReference;
import recoder.list.CompilationUnitMutableList;
import recoder.list.ModifierArrayList;
import recoder.list.ModifierMutableList;
import recoder.list.ParameterDeclarationArrayList;

public class InstanceAllocationMethodBuilder extends RecoderModelTransformer {

    public static final String IMPLICIT_INSTANCE_ALLOCATE = "<allocate>";


    public InstanceAllocationMethodBuilder
    (CrossReferenceServiceConfiguration services, 
            CompilationUnitMutableList units) {
        super(services, units);      
    }
    
    /**
     * creates a method declaration with no implementation. The methods intention is
     * to allocate a new object of the type it is declared in and to return it.
     * The functionality will be described using taclets
     */
    private MethodDeclaration createAllocateMethod(ClassDeclaration type) {
        ModifierMutableList modifiers = new ModifierArrayList(2);
        modifiers.add(new Private());
        modifiers.add(new Static());    
        
        ParameterDeclarationArrayList pdal = new ParameterDeclarationArrayList(0);
  
        MethodDeclaration md =  new MethodDeclaration
            (modifiers, 
             new TypeReference
             ((Identifier)type.getIdentifier().deepClone()), 
             new ImplicitIdentifier(IMPLICIT_INSTANCE_ALLOCATE), 
             pdal, 
             null, null);
        md.makeAllParentRolesValid();
        return md;
    }


    protected void makeExplicit(TypeDeclaration td) {
        if (td instanceof ClassDeclaration) {
            attach(createAllocateMethod((ClassDeclaration)td), td, 
                    td.getMembers().size());
//          java.io.StringWriter sw = new java.io.StringWriter();
//          services.getProgramFactory().getPrettyPrinter(sw).visitClassDeclaration((ClassDeclaration)td);
//          System.out.println(sw.toString());
//          try { sw.close(); } catch (Exception e) {}  
        }

    }

}
