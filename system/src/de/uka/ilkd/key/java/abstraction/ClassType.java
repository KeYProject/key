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

/**
   A program model element representing class types.
   @author AL
   @author RN
 */
public interface ClassType extends Type, Member, ClassTypeContainer {

    /**
       Checks if this class type denotes an interface.
       @return <CODE>true</CODE> if this object represents an interface,
       <CODE>false</CODE> if it is an ordinary class.
     */
    boolean isInterface();

    /**
       Checks if this member is abstract. An interface will report
       <CODE>true</CODE>.
       @return <CODE>true</CODE> if this member is abstract,
       <CODE>false</CODE> otherwise.
       @see #isInterface()
     */
    boolean isAbstract();
    
    /** 
	Returns the array of locally declared supertypes of this class type.
	@return the array of locally defined supertypes of this type.
    */
    ImmutableList<KeYJavaType> getSupertypes();
    
    /** 
	Returns the array of all supertypes of this class type,
	in topological order, including the class type isself as first element.
	The order allows to resolve member overloading or overloading.
	@return the array of all supertypes of this type in topological order.
    */
    ImmutableList<ClassType> getAllSupertypes(Services services);

    /** 
	Returns the fields locally defined within this class type.
	@return the array of field members of this type.
    */
    ImmutableList<Field> getFields(Services services);

    
    /** 
	Returns all visible fields that are defined in this class type
	or any of its supertypes. The fields are in topological order
	with respect to the inheritance hierarchy.
	@return the array of visible field members of this type and its
	supertypes.
    */
    ImmutableList<Field> getAllFields(Services services);

    /** 
	Returns the methods locally defined within this class type.
	@return the array of methods of this type.
    */    
    ImmutableList<Method> getMethods(Services services);

    /** 
	Returns all visible methods that are defined in this class type
	or any of its supertypes. The methods are in topological order
	with respect to the inheritance hierarchy.
	@return the array of visible methods of this type and its supertypes.
    */    
    ImmutableList<Method> getAllMethods(Services services);

    /** 
	Returns the constructors locally defined within this class type.
	@return the array of constructors of this type.
    */
    ImmutableList<Constructor> getConstructors(Services services);
    
    /** 
	Returns all class types that are inner types of this class type,
	including visible inherited types.
	@return an array of class types that are members of this type
	or any of its supertypes.
	@see #getAllSupertypes
    */
    ImmutableList<ClassType> getAllTypes(Services services);

}
