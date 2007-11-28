// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.ConstructorDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.speclang.ListOfOperationContract;
import de.uka.ilkd.key.speclang.SLListOfOperationContract;

public class JavaModelMethod implements ModelMethod, Contractable {

    private ProgramMethod method;
    private String preCond=null;
    private String postCond=null;
    private String modifies=null;
    private JavaModelClass contClass;

    public JavaModelMethod(ProgramMethod pm, String rootDir, Services services) {
	this.method = pm;
	contClass = new JavaModelClass(pm.getContainerType(), rootDir, services);
    }

    public ModelClass getContainingClass() {
	return contClass;
    }

    public ProgramMethod getProgramMethod() {
	return method;
    }

    public String getContainingClassName() {
	return method.getContainerType().getName();
    }

    public String getContainingPackage() {
	return contClass.getContainingPackage();
    }
    
    // return signature of form name(arg1: type1; arg2: type2 ...)
    // and translates Java types to OCL types
    public String getCallSignature() {
	return getCallSignature(true);
    }

    public int getNumParameters() {
        return 0;//%%%
    }
    
    public String getParameterNameAt(int i){
	return "";//%%%
    }

    public String getParameterTypeAt(int i){
	return "";//%%%
    }
    
    public String getResultType() {
        return "";//%%%
    }

    private String toOCL(String s, boolean doit) {
	if (!doit) {
	    return s;
	} else {
	    return transformTypeJava2OCL(s);
	}
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


    // return signature of form name(arg1: type1; arg2: type2 ...)
    public String getCallSignature(boolean translateJavaType2OCLTypes){
	StringBuffer res = new StringBuffer(getName()+"(");
	MethodDeclaration md = method.getMethodDeclaration();
	for (int i=0; i<md.getParameterDeclarationCount(); i++) {
	    de.uka.ilkd.key.java.declaration.VariableSpecification vs 
		= md.getParameterDeclarationAt(i).getVariableSpecification();
	    res.append(vs.getName());
            res.append(": ");
	    res.append(toOCL(vs.getType().getName(),translateJavaType2OCLTypes));
	    if (i<md.getParameterDeclarationCount()-1) res.append("; ");
	}
	res.append(")");
	if (md.getTypeReference()!=null) {
	    res.append(":"+toOCL(md.getTypeReference().getName(), 
				   translateJavaType2OCLTypes));
	}
	return res.toString();
    }

    public String getName(){
	return method.getMethodDeclaration().getProgramElementName().toString();
    }

    public boolean isVoid() {
	return method.getMethodDeclaration().getTypeReference()==null;
    }

    public boolean isConstructor() {
	return (method.getMethodDeclaration() 
		instanceof ConstructorDeclaration); 
    }

    public boolean isPrivate() {
	return method.isPrivate();
    }

    public String getTagContent(String keyword) {
	String res=null;
	MethodDeclaration md = method.getMethodDeclaration();
	Comment[] comments = md.getComments();
	for(int i=0; comments!=null && i<comments.length; i++) {
	    String s = comments[i].getText();
	    int start = s.indexOf(keyword);
	    if (start>=0) {
		int end = s.indexOf("@", start+1);
		int end2 = s.indexOf("\n", start+1);
		if (end2>=0 && end2<end) end = end2;
		if (end<0) {
		    end = s.length()-2;
		}
		res = s.substring(start+keyword.length(), end);
		
	    }	
	}
	return res==null ? null : res.trim();
    }

    // returns precondition if any, else ""
    public String getMyPreCond() {
	if (preCond==null) {
	    preCond=getTagContent("@preconditions");
	    if (preCond==null) preCond="";
	} 
	return preCond;	    
    }

    public String getMyModifClause() {
	if (modifies==null) {
	    modifies=getTagContent("@modifies");
	} 
	return modifies;	    
    }

    /**
     * returns true if <code>method</code> is a model method.
     */
    public boolean isModel() {
        return method.isModel();
    }

    // set modifies clause
    public void setMyModifClause(String modifClause) {
	modifies=modifClause;
    }

    public boolean isQuery() {
	return "".equals(getMyModifClause());
    }

    // set precondition
    public void setMyPreCond(String precond) {
	preCond=precond;
    }

    // returns precondition of parent if any, else ""
    public String getParentPreCond() {
	return "";//%%
    }

    public ModelMethod getParentMethod(){
	return null;//%%
    }

    public String getMyPostCond() {
	if (postCond==null) {
	    postCond=getTagContent("@postconditions");
	    if (postCond==null) postCond="";
	} 
	return postCond;	    
    }

    public void setMyPostCond(String postcond) {
	postCond=postcond;
    }

    public String getParentPostCond() {
	return "";//%%
    }

    // set/get GF abstract syntax representation of pre-/postconditions
    public String getMyGFAbs() {
	return "";//%%
    }

    public void setMyGFAbs(String abs) {
	return;//%%
    }

    public boolean hasOrigParent() {
	return false;//%%
    }

    public String getActXmifile(){
	return null;
    }

    public String toString() {
       return getContainingClass().getClassName() + "::" + getCallSignature();
    }

    public int hashCode() {
	return getProgramMethod().hashCode()*13+getContainingClass().hashCode();
    }

    public boolean equals(Object o) {
	if (!(o instanceof JavaModelMethod)) {
	    return false;
	}
	JavaModelMethod jmm = (JavaModelMethod)o;
	return getProgramMethod().equals(jmm.getProgramMethod()) &&
	    getContainingClass().equals(jmm.getContainingClass());
    }
    
    public ListOfOperationContract getMyOperationContracts() {
        return SLListOfOperationContract.EMPTY_LIST;//%%
    }

    public boolean equalContractable(Contractable c) {
    	return equals(c);
    }
}
