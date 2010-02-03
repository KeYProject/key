// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together;

import java.util.Enumeration;
import java.util.Iterator;
import java.util.Vector;

import com.togethersoft.openapi.rwi.*;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.casetool.UMLModelClass;

/** represents a method of the Together model. It is backed by the
 * corresponding Together RWI model element, but it is independent in
 * a sense that changing the together project allows to access all
 * methods unless they are specifically marked.
 */
public class TogetherModelMethod extends TogetherReprModel 
    implements ModelMethod {

    // which element of the model do I represent
    private final RwiMember orig;     
    private RwiModel currRwiModel;
    private RwiDiagram currRwiDiagram;
    
    private RwiMember origParent;
    private boolean origParentAlreadySet = false;

    private boolean parameterListComputed = false;
    private Vector paraNames = new Vector();
    private Vector paraTypes = new Vector();

    private UMLModelClass containingClass;
    private String retTypeString;
    private String callSig;
    private String callSigOCL;
    private String callSigQualif;   // package qualified call signature
    private String callSigQualifOCL;
    private String name;
    private String precond;
    private String postcond;
    private String modifies;
    private String stereotype;
    private boolean constr;
    private boolean priv;
    private int hash = 0;


    public TogetherModelMethod(RwiMember theOrig, RwiModel model, 
				   RwiDiagram diag) { 
	orig = theOrig;
	currRwiModel = model;
	currRwiDiagram = diag;
	this.containingClass = createContainingClassRepr();
	retTypeString = orig.getProperty(RwiProperty.RETURN_TYPE);
	callSigOCL=createCallSignature(true);
	callSig=createCallSignature(false);
    callSigQualifOCL = createCallSignatureQualified(true);
    callSigQualif = createCallSignatureQualified(false);
	name = orig.getProperty(RwiProperty.NAME);
	precond = orig.getProperty("preconditions");
	postcond = orig.getProperty("postconditions");
	modifies = orig.getProperty("modifies");
	stereotype = orig.getProperty("stereotype");	   
	constr = orig.getProperty(RwiProperty.CONSTRUCTOR) != null;
	priv = orig.getProperty(RwiProperty.PRIVATE) != null;
    }

    /** returns the together original object representing this
     * method. Could be invalidated since a new project has been
     * loaded.
     */
    public RwiMember getOrig() {
	return orig;
    }

    public UMLModelClass createContainingClassRepr(){
	RwiNode localContainingClass = orig.getContainingNode();
	return new TogetherModelClass(localContainingClass, currRwiModel, 
					  currRwiDiagram);
    }

    public ModelClass getContainingClass() {
	return containingClass;
    }

    public String getContainingPackage(){
	return getContainingClass().getContainingPackage();
    }

    public String getContainingClassName(){
	return getContainingClass().getClassName();	
    }

    public boolean isVoid() {
	return !isConstructor() 
		&& (retTypeString==null || "void".equals(retTypeString));
    }
    
    public int getNumParameters() {
        if (!parameterListComputed) 
            getCallSignature();
        return paraNames.size();
    }

    public String getParameterNameAt(int i) {
	if (!parameterListComputed) 
	    getCallSignature();
	return paraNames.elementAt(i).toString();
    }

    public String getParameterTypeAt(int i) {
	if (!parameterListComputed) 
	    getCallSignature();
	return paraTypes.elementAt(i).toString();
    }
    
    public String getResultType() {
	if(isConstructor()) {
	    return containingClass.getFullClassName();
	} else {
	    String s = orig.getProperty(RwiProperty.RETURN_TYPE);
	    return (s.equals("void") ? null : s);
	}
    }
    
    public String getCallSignature() {
	return getCallSignature(true);
    }
 
   
    public String getCallSignature(boolean translateJavaType2OCLTypes){
	if (translateJavaType2OCLTypes) {
	    return callSigOCL;
	} else {
	    return callSig;
	}
    }

    /** as getCallSignature, but param and return types are qualified */
    public String getCallSignatureQualified(boolean java2ocl) {
        return java2ocl ? callSigQualifOCL : callSigQualif;
    }

    /** as getCallSignature, but param and return types are qualified */
    public String getCallSignatureQualified() {
        return getCallSignatureQualified(true);
    }

    // returnvalue is adapted to the needs of OCL-parser from dresden
    public String createCallSignature(boolean translateJavaType2OCLTypes){
	String argString = orig.getProperty(RwiProperty.PARAMETERS_TEXT);
	// argString has the form type1 arg1, type2 arg2, ...
	// parser expects of form arg1: type1; arg2: type2
	String parserString = shuffleForParser
	    (argString, translateJavaType2OCLTypes);
	    
	String returnTypeString = orig.getProperty(RwiProperty.RETURN_TYPE);
	String retSuffix = null;
	if (returnTypeString == null){
	    // We have a constructor method ...
	    // Leave it empty (because of the syntax used by the OCL parser ...
	    retSuffix = "";
	} else 
	    if (returnTypeString.equals("void")){
		// Leave it empty (because of the syntax used by the OCL parser ...
		retSuffix = "";
	    } else {
		if (translateJavaType2OCLTypes) 
		    retSuffix = ":" + transformTypeJava2OCL(returnTypeString);
		else 
		    retSuffix = ":" + returnTypeString;
	    }
	return orig.getProperty(RwiProperty.NAME)+"("+ parserString +")" + retSuffix;
    }

    /** take a fully qualified type name, remove qualification if it is not needed.
      * The fullName must not end in "." */
    private String fullname2qualname(String fullName, boolean java2ocl)
    {
        int ix = fullName.lastIndexOf(".");
        if (ix == -1) {
            return transformTypeJava2OCL(fullName);
        } else {
            String pkg = fullName.substring(0,ix);
            String shortName = fullName.substring(ix+1); 
            if (! pkg.equals(getContainingPackage())) { 
                // qualification necessary
                if (java2ocl) {
                    return pkg.replaceAll("\\.","::") + "::" + shortName;
                } else {
                    return fullName;
                }
            } else {
                // no qualification necessary
                return shortName;
            }
        }
    }
    
    
    private String sequentialize(String keyarrayof, boolean isArray, boolean java2ocl) {
            String result;
            if (java2ocl) {
	            if (isArray) {
	                    if (keyarrayof.indexOf("KeYArrayOf") > -1) {
	                            result = keyarrayof.replaceFirst(
	                                    "KeYArrayOf", 
	                                    "Sequence (") + ")";
	                    } else {
	                            result = "Sequence (" + keyarrayof + ")";
	                    }
	            } else {
	                    result = keyarrayof;
	            }
            } else {
                    result = keyarrayof; //conserve a buggy behaviour %%
                    					 //daniels does not want to break anything
            }
            return result;
    }
    
    /**
     * qualify types with package 
     * @param java2ocl true: OCL notation (package::class, Sequence(Integer)),
     *  false: java notation (package.class, int[])
     * @return a String representing the fully qualified call signature
     */
    public String createCallSignatureQualified(boolean java2ocl) {
        String retTypeUnqual = orig.getProperty(RwiProperty.RETURN_TYPE);
        //hack is needed, since orig.getProperty(RwiProperty.RETURN_TYPE_REFERENCED_ELEMENT)
        //throws away the knowledge, if the return type is a package or not.        
        boolean isArray = retTypeUnqual == null ? 
                false : (retTypeUnqual.indexOf("[") > -1);
        if (java2ocl && retTypeUnqual != null) {         
            retTypeUnqual = transformTypeJava2OCL(retTypeUnqual);
            retTypeUnqual = sequentialize(retTypeUnqual, isArray, java2ocl);
        }

        String retType;
        String retRef = orig.getProperty(RwiProperty.RETURN_TYPE_REFERENCED_ELEMENT);
        if (retRef != null) {
            RwiElement foundElem = currRwiModel.findElement(retRef);
            if (foundElem != null) {
                String fullName = foundElem.getProperty(
                    RwiProperty.FULL_NAME);
                String qualName = fullname2qualname(fullName, java2ocl);
                qualName = sequentialize(qualName, isArray, java2ocl);
                retType = qualName;
            } else {
                // could not qualify
                retType = retTypeUnqual;
            }
        } else {
            // retRef == null
            retType = retTypeUnqual;
        }
           

        Enumeration rwiParamsEnum = 
            orig.properties(RwiProperty.PARAMETER);
        Vector paramNames = new Vector(); // elemtype: String
        Vector paramTypesUnqual = new Vector(); // elemtype: String
        Vector paramTypes = new Vector(); // elemtype: String
        
        while (rwiParamsEnum.hasMoreElements()) {
            RwiProperty param = (RwiProperty) rwiParamsEnum.nextElement();
            RwiPropertyMap subprops = param.getSubproperties();
            paramNames.add(subprops.getProperty(RwiProperty.NAME));
            String paramTypeUnqual = subprops.getProperty(RwiProperty.TYPE);
            isArray = (paramTypeUnqual.indexOf("[") > -1);
            if (java2ocl) { 
                paramTypeUnqual = transformTypeJava2OCL(paramTypeUnqual);
                paramTypeUnqual = sequentialize(paramTypeUnqual, isArray, java2ocl);
            }
            paramTypesUnqual.add(paramTypeUnqual);
            
            // qualified type
            String uniqueTypeName = subprops.getProperty(
                RwiProperty.TYPE_REFERENCED_ELEMENT);
            RwiElement foundElem = currRwiModel.findElement(uniqueTypeName);
            if (foundElem != null) { // success not guaranteed
                // (Together docs says e.g. it might not be in classpath)
                // it might be a basic type e.g. int
                String fullName = foundElem.getProperty(RwiProperty.FULL_NAME);
                String qualName = fullname2qualname(fullName, java2ocl);
                qualName = sequentialize(qualName, isArray, java2ocl);
                paramTypes.add(qualName);
            } else { 
                // qualification failed: just add unqualified type 
                // or should we raise an exception?
                paramTypes.add(paramTypeUnqual);
            }
        }
    
        // add parameters to signature:
        String sig = "(";
        Iterator i = paramNames.iterator();
        Iterator j = paramTypes.iterator(); 
        while (i.hasNext() && j.hasNext()) { // Vector length should be the same
            String pName = (String) i.next();
            String pType = (String) j.next();
            if (java2ocl) {
                sig += pName + " : " + pType;
            } else {
                sig += pType + " " + pName;
            }
            if (i.hasNext() && j.hasNext()) {
                sig += ", ";
            }
        }
        
        // add return type:
        sig += ")";
        if (retType != null && ! retType.equals("void")) {
            sig += " : " + retType;
        }
        
        return orig.getProperty(RwiProperty.NAME) + sig;
    }

    public String getName(){ 
	return name; 
    }


    // besides shuffling the arg with the type we also
    // transform some java-types to ocl-types
    private String shuffleForParser(String argString, 
				    boolean translateJavaType2OCLTypes){
	argString=argString.trim();
	if (argString.equals("")){return "";}
	String resString = "";
	int actPos = 0;
	int nextSpace, nextColon;
	boolean through = false;
	String optColon = "";
	String actArgument, actTypeJava, actTypeOcl;
	while (!through){
	    //skip "final "
	    if(argString.substring(actPos).startsWith("final ")) {
		actPos += 6;
	    }
	    
	    nextSpace = argString.indexOf(' ', actPos);
	    nextColon = argString.indexOf(',', actPos);
	    if (nextColon == -1){
		// end of argString 
		through = true;
		nextColon = argString.length();
	    }
	    if (actPos > 0) {optColon = "; ";}
	    actArgument = argString.substring(nextSpace+1, nextColon);
	    actTypeJava = argString.substring(actPos, nextSpace);
	    
	    // store parameters in vector
	    if (!parameterListComputed){
		paraNames.addElement(actArgument);
		paraTypes.addElement(actTypeJava);
	    }

	    if (translateJavaType2OCLTypes)
		actTypeOcl = transformTypeJava2OCL(actTypeJava);
	    else
		actTypeOcl = actTypeJava;
	    resString = resString + optColon + actArgument + ": " + actTypeOcl;
	    actPos = nextColon + 2;
	}
	parameterListComputed = true;
	return resString;
    }

    public static String transformTypeJava2OCL(String aJavaType){
        if ("int".equals(aJavaType) || 
            "byte".equals(aJavaType) ||
            "char".equals(aJavaType) ||
            "short".equals(aJavaType) ||
            "long".equals(aJavaType)){
            return "Integer";
        }
        else if ("boolean".equals(aJavaType)) {return "Boolean";}
        else if (aJavaType.endsWith("[]")) {
            String base = transformTypeJava2OCL(aJavaType.substring
                                                (0,aJavaType.length()-2));
            return "KeYArrayOf"+base;

        }
        else {
            return aJavaType;
        }
    }


    // looks if orig has a parent and set it if needed
    // parent means for methods the next occurrence of the method
    //  in the inheritance hierarchy which has an own pre/post specification
    private RwiMember getOrigParent(){
	if (origParentAlreadySet){
	    return origParent;
	}else{
	    // we ask our containingNode to do the job
	    RwiNode localContainingClass = orig.getContainingNode();
	    TogetherModelClass contClassRepr = 
		new TogetherModelClass(localContainingClass, currRwiModel, 
					   currRwiDiagram);
	    String myUniqueName = orig.getUniqueName();

	    RwiMember candParent;
 	    // findParentMeth returns the next Meth-Declaration
	    // in the inheritance hierarchy above
	    candParent= contClassRepr.findParentMeth(myUniqueName);
	    if (candParent==null){
		return null;
	    }
	    if ((candParent.getProperty("preconditions") != null || 
		 candParent.getProperty("postconditions") != null)){
		// candParent has its own specification
 		origParent = candParent;
	    }else{
 		// otherwise we ask candParent for its parent
		origParent=
		    (new TogetherModelMethod(candParent, currRwiModel, 
						 currRwiDiagram)).getOrigParent();
	    }
	    origParentAlreadySet = true;
	}
	return origParent;
    }




    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     * 
     */
    public String getMyOrParentPostCond() {
    	String myPre = getMyPreCond();
	String myPost = getMyPostCond();
	if (myPre.equals("") && myPost.equals("")){
	    // ask parent
	    TogetherModelMethod parentRepr = 
		new TogetherModelMethod(getOrigParent(), currRwiModel, 
					    currRwiDiagram);
	    return parentRepr.getMyPostCond();
	}else{
	    return myPost;
	}
    }


    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened);
     * we ask the parent only when method does not have neither precond
     * nor postcond.  
     */
    public String getMyOrParentPreCond() {
	String myPre = getMyPreCond();
	String myPost = getMyPostCond();
	if (myPre.equals("") && myPost.equals("")){
	    // ask parent
	    TogetherModelMethod parentRepr = 
		new TogetherModelMethod(getOrigParent(), currRwiModel, 
					    currRwiDiagram);
	    return parentRepr.getMyPreCond(); 
	}else{
	    return myPre;
	}
    }

    public String getMyPreCond() { 
	return (precond==null) ? "" : precond;
    }

    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public void setMyPreCond(String precond){
	this.precond = precond;
	orig.setProperty("preconditions", precond);
    }
 
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public String getParentPreCond() {
	// ask parent
	TogetherModelMethod parentRepr = 
	    new TogetherModelMethod(getOrigParent(), currRwiModel, 
					currRwiDiagram);
	return parentRepr.getMyPreCond();
    }

    public String getMyPostCond() { 
	return (postcond==null) ? "" : postcond;
    }

    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public void setMyPostCond(String postcond){
	this.postcond = postcond;
	orig.setProperty("postconditions", postcond);
    }

    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public String getParentPostCond() {
	// ask parent
	TogetherModelMethod parentRepr = 
	    new TogetherModelMethod(getOrigParent(), currRwiModel, 
					currRwiDiagram);
	return parentRepr.getMyPostCond();
    }

    public String getMyModifClause() {
	return (modifies==null) ? "" : modifies;
    }
    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public void setMyModifClause(String modifClause) {
	modifies = modifClause;
    	orig.setProperty("modifies", modifClause);
    }

    public boolean isQuery() {
	return ("query".equals(stereotype));
    }

    
    public boolean isConstructor() {
	return constr;
    }


    public boolean isPrivate() {
	return priv;
    }

    public String getMyGFAbs() {
    	String result = orig.getProperty("GFAbstractSyntax");
    	if (result == null) {
	    return "";
	} else {
	    return result;
	}
    }
    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened)
     */
    public void setMyGFAbs(String abs) {
    	orig.setProperty("GFAbstractSyntax", abs);
    }

    public boolean hasOrigParent() {
        return (getOrigParent() != null);
    }
    
    /** relies on a valid backing RWI model element, i.e. the together
     * project is still valid (opened);
     * gets the overridden methods in the superclass if exists else null
     */
    public ModelMethod getParentMethod() {
	if (hasOrigParent()) {
	    return new TogetherModelMethod(getOrigParent(), currRwiModel, 
					       currRwiDiagram);
	} else
	    return null;
    }
    
    public String toString() {
       return getContainingClass().getClassName() + "::" + getCallSignature();
    }

    public boolean equals(Object cmp) {
	if (cmp==null) return false;
	if (!(cmp instanceof TogetherModelMethod)) return false;
	return toString().equals(cmp.toString());
    }

    public int hashCode() {
	return hash==0 ? (hash=toString().hashCode()) : hash;
    }    
}
