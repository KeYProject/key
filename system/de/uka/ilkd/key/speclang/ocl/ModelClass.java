package de.uka.ilkd.key.speclang.ocl;

import java.util.Set;
import java.util.Vector;

import de.uka.ilkd.key.collection.ImmutableList;


public interface ModelClass {

    public abstract String getClassName();

    public abstract String getFullClassName();

    // returns the invariant of the class if any, else ""
    public abstract String getMyInv();

    // returns the throughout of the class if any, else ""
    public abstract String getMyThroughout();

    //returns the package containing this class. If there
    // is none, returns null
    public abstract String getContainingPackage();

    public abstract String[] getClassesInPackage();

    public abstract String getRootDirectory();

    /**
     * Returns all supertypes of the class, including implemented interfaces.
     */ 
    ImmutableList<ModelClass> getMyParents();
    
    // returns ReprModelMethod
    Vector getOps();
    
    public abstract Set getAllClasses();
}
