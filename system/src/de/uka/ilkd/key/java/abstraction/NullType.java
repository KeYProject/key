// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.expression.Literal;

/**
   A program model element representing the null type.
   @author AL
   @author RN
 */
public class NullType implements ClassType {

    public static final NullType JAVA_NULL = new NullType();
    private NullType(){}

    /**
       The name of this type.
     */
    public static final String NULL = "null";

    /**
       Returns the name of this element.
       @return <CODE>"null"</CODE>.
     */
    public String getName() {
	return NULL;
    }

    /**
       Returns the name of this element.
       @return <CODE>"null"</CODE>.
     */
    public String getFullName() {
	return NULL;
    }

    /**
       Checks if this member is final.
       @return <CODE>true</CODE>.
     */
    public boolean isFinal() {
	return true;
    }

    /**
       Checks if this member is static.
       @return <CODE>true</CODE>.
     */
    public boolean isStatic() {
	return true;
    }

    /**
       Checks if this member is private.
       @return <CODE>false</CODE>.
     */
    public boolean isPrivate() {
	return false;
    }

    /**
       Checks if this member is protected.
       @return <CODE>false</CODE>.
     */
    public boolean isProtected() {
	return false;
    }

    /**
       Checks if this member is public.
       @return <CODE>true</CODE>.
     */
    public boolean isPublic() {
	return true;
    }

    /**
       Checks if this member is strictfp.
       @return <CODE>false</CODE>.
     */
    public boolean isStrictFp() {
	return false;
    }

    /**
       Checks if this class type denotes an interface.
       @return <CODE>false</CODE>.
     */
    public boolean isInterface() {
        return false;
    }

    /**
       Checks if this member is abstract. 
       @return <CODE>false</CODE>.
     */
    public boolean isAbstract() {
        return false;
    }

    /** 
	Returns the array of locally declared supertypes of this class type.
	@return the array of locally defined supertypes of this type.
    */
    public ImmutableList<KeYJavaType> getSupertypes(){
        return null;
    }
    
    /** 
	Returns the array of all supertypes of this class type,
	in topological order, including the class type isself as first element.
	The order allows to resolve member overloading or overloading.
	@return the array of all supertypes of this type in topological order.
    */
    public ImmutableList<ClassType> getAllSupertypes(Services services){
        return null;
    }

    /** 
	Returns the fields locally defined within this class type.
	@return the array of field members of this type.
    */
    public ImmutableList<Field> getFields(Services services){
        return null;
    }

    
    /** 
	Returns all visible fields that are defined in this class type
	or any of its supertypes. The fields are in topological order
	with respect to the inheritance hierarchy.
	@return the array of visible field members of this type and its
	supertypes.
    */
    public ImmutableList<Field> getAllFields(Services services){
        return null;
    }

    /** 
	Returns the methods locally defined within this class type.
	@return the array of methods of this type.
    */    
    public ImmutableList<Method> getMethods(Services services){
        return null;
    }

    /** 
	Returns all visible methods that are defined in this class type
	or any of its supertypes. The methods are in topological order
	with respect to the inheritance hierarchy.
	@return the array of visible methods of this type and its supertypes.
    */    
    public ImmutableList<Method> getAllMethods(Services services){
        return null;
    }

    /** 
	Returns the constructors locally defined within this class type.
	@return the array of constructors of this type.
    */
    public ImmutableList<Constructor> getConstructors(Services services){
        return null;
    }
    
    /** 
	Returns all class types that are inner types of this class type,
	including visible inherited types.
	@return an array of class types that are members of this type
	or any of its supertypes.
	@see #getAllSupertypes
    */
    public ImmutableList<ClassType> getAllTypes(Services services){
        return null;
    }

    public Package getPackage() {
	return null;
    }


    /** 
     * returns the default value of the given type 
     * according to JLS Sect. 4.5.5 
     * @return the default value of the given type 
     * according to JLS Sect. 4.5.5
     */
    public Literal getDefaultValue() {
	return null;
    }

    public boolean equals(Object o){
        return o == JAVA_NULL;
    }
    
    public int hashCode() {
        //singleton
        return System.identityHashCode(this);
    }
}
