package de.uka.ilkd.key.java.recoderext;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.Public;
import recoder.java.declaration.modifier.Static;
import recoder.java.reference.TypeReference;
import recoder.list.*;

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
        modifiers.add(new Public());
        modifiers.add(new Static());    
        
        ParameterDeclarationArrayList pdal = new ParameterDeclarationArrayList(0);
  
        MethodDeclaration md =  new MethodDeclaration
            (modifiers, 
             new TypeReference(getId(type)), 
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
