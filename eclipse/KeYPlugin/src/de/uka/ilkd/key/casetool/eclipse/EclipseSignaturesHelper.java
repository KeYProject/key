//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                  Universitaet Koblenz-Landau, Germany
//                  Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.eclipse;

import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;

//Also used by VisualDebugger.
/**
 * @author Marius Hillenbrand
 */
public class EclipseSignaturesHelper {

    public static String determineJavaType(String eclipseSignature, IType surroundingType) {

	switch(eclipseSignature.charAt(0)) {

	case Signature.C_ARRAY: // this parameter is an array

	    int depth = Signature.getArrayCount(eclipseSignature);

	    StringBuffer type = new StringBuffer(
		    determineJavaType(Signature.getElementType(eclipseSignature), surroundingType));
	    // array type is <element type> ([])+, now create the []s

	    for(int i=0; i<depth; i++) {
		type.append('['); type.append(']');
		// this is probably much faster, than handling String-objects ?!		
	    }
	    return type.toString();
		// primitive types:
	case Signature.C_BOOLEAN:
	    return "boolean";

	case Signature.C_BYTE:
	    return "byte";

	case Signature.C_CHAR:
	    return "char";

	case Signature.C_DOUBLE:
	    return "double";

	case Signature.C_FLOAT:
	    return "float";

	case Signature.C_INT:
	    return "int";

	case Signature.C_LONG:
	    return "long";

	case Signature.C_SHORT:
	    return "short";

	    // arbitrary types with fully-qualified name
	case Signature.C_RESOLVED:
	    return eclipseSignature.substring(1, eclipseSignature.length()-1);
	    // eclipse input is "Lpackage.Type;", so
	    // cut off the first and last character

	    // arbitrary types with unresolved names
	case Signature.C_UNRESOLVED:
	    String unqualifiedTypeName = eclipseSignature.substring(1, eclipseSignature.length()-1);
	    try {
		String[][] resolvedTypes = surroundingType.resolveType(unqualifiedTypeName);					
		if(resolvedTypes!=null && resolvedTypes.length>0) {
		    return (resolvedTypes[0][0].equals("") ? "" : resolvedTypes[0][0] + ".")
		    + resolvedTypes[0][1];
		} else {
		    return null;
		}

	    } catch (JavaModelException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	    }

	}
	throw new RuntimeException("Eclipse Signature type "+eclipseSignature+"not checked, add support !!");
    }
}
