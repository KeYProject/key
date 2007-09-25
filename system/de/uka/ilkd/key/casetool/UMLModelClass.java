// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/**
 * ModelClass represents a UML class modeled in the casetool.
 *
 * Bug: In the String-based methods, interfaces are not considered yet. 
 *      (See also comment in together.TogetherReprModelClass.
 *      Consequentely, classes have only one parent.
 */


package de.uka.ilkd.key.casetool;

import java.util.Vector;

import de.uka.ilkd.key.java.Services;


public interface UMLModelClass extends ReprModel, ModelClass {

    // set the (OCL) invariant of the class
    void setMyInv(String inv);
	
    // set the GF abstract syntax for the invariant of the class
    void setMyInvGFAbs(String inv);

    // returns the invariant of the parent if any, else ""
    String getParentInv();
    
    // returns the classname of the parent if any, else ""
    String getParentClassName();
    
    // returns true if class has a parent
    boolean hasOrigParent();

    // returns ReprModelMethod
    Vector getOps();

    
    UMLInfo createUMLInfo(Services services);

    
    
    
    //-------------------------------------------------------------------------
    //deprecated
    //-------------------------------------------------------------------------
    
    /**@deprecated*/
    void getAssociations(HashMapOfClassifier classifiers);

}
