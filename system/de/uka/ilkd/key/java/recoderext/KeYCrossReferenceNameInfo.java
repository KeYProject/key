// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design

package de.uka.ilkd.key.java.recoderext;

import java.util.HashMap;

import recoder.ServiceConfiguration;
import recoder.abstraction.*;
import recoder.java.declaration.TypeDeclaration;
import recoder.kit.UnitKit;
import recoder.service.DefaultNameInfo;
import de.uka.ilkd.key.java.ConvertException;



/**
 * This is a specialisation of the NameInfo interface which allows KeY to detect
 * multiple declaration of types. It stores all defined type (w/o possible some
 * array types which do not matter) in a hash table to look up.
 * 
 * If it records an attempt to register a declaration type twice, a verbose
 * conversion exception is thrown.
 * 
 * An instance of this class is created in
 * {@link KeYCrossReferenceServiceConfiguration}.
 * 
 * @author MU
 * 
 */
public class KeYCrossReferenceNameInfo extends DefaultNameInfo {
    
    // this somewhat doubles name2type in DefaultNameInfo to which we have no access
    private HashMap<String, ClassType> classtypes = new HashMap<String, ClassType>(); 
    
    public KeYCrossReferenceNameInfo(ServiceConfiguration config) {
        super(config);
    }
   
    /**
     * register a class type.
     * 
     * @param ct
     *                class type to register
     * @throws ConvertException
     *                 if there was already a different type registered for the
     *                 same name
     */
    @Override
    public void register(ClassType ct) {
        
        String name = ct.getFullName();
        ClassType old = classtypes.get(name);
        if(old != null && ct != old) {
            String d1, d2;
            if (ct instanceof TypeDeclaration) {
                d1 = UnitKit.getCompilationUnit((TypeDeclaration) ct).getOriginalDataLocation().toString();
            } else {
                d1 = ct.toString();
            }
            if (old instanceof TypeDeclaration) {
                d2 = UnitKit.getCompilationUnit((TypeDeclaration) old).getOriginalDataLocation().toString();
            } else {
                d2 = old.toString();
            }
            throw new ConvertException("Datatype " + name + " declared twice: Once in " + d1 + " and once in " + d2);
        }
        
        super.register(ct);
        
        classtypes.put(name, ct);
    }

    /**
     * unregister a class type. This happens for instance when removing an
     * EnumDeclaration and inserting an EnumClassDeclaration instead
     * 
     * @param fullname
     *                name of the type to be unregistered
     */
    @Override
    public void unregisterClassType(String fullname) {
        super.unregisterClassType(fullname);
        classtypes.remove(fullname);
    }

    /*
     * just to make sure that classtypes captures all non-array types.
     */
    @Override
    public Type getType(String name) {
        Type t = super.getType(name);
        if(t instanceof ClassType)
            classtypes.put(name, (ClassType)t);
        return t;
    }

}
