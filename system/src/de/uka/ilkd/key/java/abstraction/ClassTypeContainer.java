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

/**
   A program model element that may contain class types.
 */
public interface ClassTypeContainer extends ProgramModelElement {

    /** 
	Returns the class types locally defined within this container.
	Returns inner types when this container is a class type.
	@return an array of contained class types.
    */
    //    ClassType[] getTypes();

    /**
       Returns the package this element is defined in. Packages
       have no recursive scope and report themselves.
       @return the package of this element.
     */
    // Package getPackage();
    
    /**
       Returns the enclosing package or class type, or method.
       A package will report <tt>null</tt>, a methods its enclosing
       class.
       @return the container of this element.
     */
    // ClassTypeContainer getContainer();

}
