package de.uka.ilkd.key.casetool;

import java.util.Set;
import java.util.Vector;

import de.uka.ilkd.key.speclang.ListOfClassInvariant;


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

    /**
     * Returns the invariants of the class.
     */
    public abstract ListOfClassInvariant getMyClassInvariants();

    /**
     * Returns the throughout invariants of the class.
     */
    public abstract ListOfClassInvariant getMyThroughoutClassInvariants();

}
