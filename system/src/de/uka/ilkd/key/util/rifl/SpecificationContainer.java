package de.uka.ilkd.key.util.rifl;

import recoder.java.declaration.MethodDeclaration;

/** Container for parsed RIFL specifications.
 * Each query returns the assigned security level for an element represented as a String,
 * or null if the element is not assigned a level.
 * RIFL specifications are not validated in any way.
 * @author bruns
 *
 */
public interface SpecificationContainer {
    
    public String returnValue (String inPackage, String inClass, String methodName, String[] paramTypes);
    
    /** Return the security level of the method return, represented as a String. */
    public String returnValue (MethodDeclaration md);
    
    public String parameter (String inPackage, String inClass, String methodName, String[] paramTypes, int index);
    public String parameter (MethodDeclaration md, int index);

}
