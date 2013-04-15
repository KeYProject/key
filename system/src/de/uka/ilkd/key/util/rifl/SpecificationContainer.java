package de.uka.ilkd.key.util.rifl;

import recoder.java.declaration.MethodDeclaration;

public interface SpecificationContainer {
    
    public String returnValue (String inPackage, String inClass, String methodName, String[] paramTypes);
    public String returnValue (MethodDeclaration md);
    
    public String parameter (String inPackage, String inClass, String methodName, String[] paramTypes, int index);
    public String parameter (MethodDeclaration md, int index);

}
