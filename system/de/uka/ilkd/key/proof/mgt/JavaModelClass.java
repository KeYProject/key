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

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import de.uka.ilkd.key.casetool.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;
import de.uka.ilkd.key.speclang.SLListOfClassInvariant;


public class JavaModelClass implements ModelClass {

    private final KeYJavaType kjt;
    private final String rootDir;
    private final Services services;

    public JavaModelClass(KeYJavaType kjt, String rootDir, Services services) {
	assert kjt != null;
	assert rootDir != null;
	this.kjt=kjt;
	this.rootDir=rootDir;
        this.services = services;
    }

    public KeYJavaType getKeYJavaType() {
	return kjt;
    }

    public String getClassName() {
	return kjt.getJavaType().getName();
    }

    public String getFullClassName() {
	return kjt.getJavaType().getFullName();
    }

    // returns the invariant of the class if any, else ""
    public String getMyInv() {
	return "";//%%
    }

    // returns the throughout of the class if any, else ""
    public String getMyThroughout(){
	return "";//%%

    }

    // set the (OCL) invariant of the class
    public void setMyInv(String inv){

    }
	
    // set the GF abstract syntax for the invariant of the class
    public void setMyInvGFAbs(String inv){

    }

    // get the GF abstract syntax for the invariant of the class
    public String getMyInvGFAbs(){
	return "";//%%

    }
    
    //returns the package containing this class. If there
    // is none, returns null
    public String getContainingPackage(){
	String classname = kjt.getFullName();
	if (classname.indexOf(".")>=0) {
	    return classname.substring(0, classname.lastIndexOf("."));
	} else {
	    return null;
	}
    }

    // return the invariant of the parent if any, else ""
    public String getParentInv(){
	return "";//%%

    }
    
    // return the classname of the parent if any, else ""
    public String getParentClassName(){

	return "";//%%
    }
    

    // returns true if class has a parent
    public boolean hasOrigParent(){
	return false;
    }


    // calls getOpNames on parent if any, else returns null
    public Vector getParentOpNames(){
	return null;
    }


    // calls getOps on parent if any, else returns null
    public Vector getParentOps(){
	return null;
    }

    // calls getOpNames on parent if any, else returns null
    public Vector getInheritedOpNames(){
	return null;
    }


    // calls getOps on parent if any, else returns null
    public Vector getInheritedOps(){
	return null;
    }


    public Vector getOpNames(){
	return null;
	
    }

    // returns ReprModelMethod
    public Vector getOps(){

	return null;
    }

    public void getAssociations(HashMapOfClassifier classifiers){

    }

    public String getText(){
	return "";//%%
    }

    public String[] getClassesInPackage(){
	return new String[0];
    }

    public String getRootDirectory(){
	return rootDir;
    }

    public Set getAllClasses(){
	Set allKJTs = services.getJavaInfo().getAllKeYJavaTypes();
        Iterator it = allKJTs.iterator();
        Set result = new HashSet();
        while (it.hasNext()) {
            result.add(new JavaModelClass((KeYJavaType)it.next(), 
                                          rootDir, services));
        }
        return result;
    }

    public String getActXmifile() {
	return "";
    }

    public int hashCode() {
	int result = 7;
	result = 13*result + getKeYJavaType().hashCode();
	result = 13*result + getRootDirectory().hashCode();
	return result;
    }

    public boolean equals(Object o) {
	if (!(o instanceof JavaModelClass)) {
	    return false;
	}
	JavaModelClass cmp = (JavaModelClass) o;
	return kjt.equals(cmp.getKeYJavaType()) &&
	    getRootDirectory().equals(cmp.getRootDirectory());
    }
    
    public ListOfClassInvariant getMyClassInvariants() {	
        return services.getSpecificationRepository().getAllInvariantsForType(getKeYJavaType());
    }

    public ListOfClassInvariant getMyThroughoutClassInvariants() {
        return SLListOfClassInvariant.EMPTY_LIST;//%%
    }
    
    public ListOfModelClass getMyParents() {
        return SLListOfModelClass.EMPTY_LIST;//%
    }
    
    public UMLInfo createUMLInfo(Services services) {
        return new UMLInfo(services, SLListOfAssociation.EMPTY_LIST);//%
    }    
    
    public String toString() {
        return getKeYJavaType()+","+getRootDirectory();
    }
}
