// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.util.rifl;

import recoder.java.declaration.FieldDeclaration;
import recoder.java.declaration.MethodDeclaration;

/**
 * Container for parsed RIFL specifications. Each query returns the assigned
 * security level for an element represented as a String, or null if the element
 * is not assigned a level. RIFL specifications are not validated in any way.
 * 
 * @author bruns
 * 
 */
public interface SpecificationContainer {

    /**
     * Return the security level of the field, represented as a String.
     * Convenience method for Recoder AST element.
     */
    public String field(FieldDeclaration fd);

    /** Return the security level of the field, represented as a String. */
    public String field(String inPackage, String inClass, String name);

    /**
     * Return the security level of the method parameter, represented as a
     * String. Convenience method for Recoder AST element.
     */
    public String parameter(MethodDeclaration md, int index);

    /**
     * Return the security level of the method parameter, represented as a
     * String.
     */
    public String parameter(String inPackage, String inClass,
            String methodName, String[] paramTypes, int index);

    /**
     * Return the security level of the method return, represented as a String.
     * Convenience method for Recoder AST element.
     */
    public String returnValue(MethodDeclaration md);

    /** Return the security level of the method return, represented as a String. */
    public String returnValue(String inPackage, String inClass,
            String methodName, String[] paramTypes);

}
