// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.casetool;

import java.util.Set;
import java.util.Vector;


public interface ModelClass {

    public abstract String getClassName();

    public abstract String getFullClassName();

    // returns the invariant of the class if any, else ""
    public abstract String getMyInv();

    // returns the throughout of the class if any, else ""
    public abstract String getMyThroughout();

    // get the GF abstract syntax for the invariant of the class
    public abstract String getMyInvGFAbs();

    //returns the package containing this class. If there
    // is none, returns null
    public abstract String getContainingPackage();

    public abstract String[] getClassesInPackage();

    public abstract String getRootDirectory();

    /**
     * Returns all supertypes of the class, including implemented interfaces.
     */ 
    ListOfModelClass getMyParents();
    
    // returns ReprModelMethod
    Vector getOps();
    
    public abstract Set getAllClasses();
}
