// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

// Modified by KeY

package de.uka.ilkd.key.java.abstraction;

import de.uka.ilkd.key.java.reference.TypeReference;

/**
   A program model element representing array types.
 */
public interface ArrayType extends Type {

    /**
     * returns the type reference to the arrays base type
     * @return the type reference to the arrays base type
     */
    TypeReference getBaseType();
    
    /**
     * returns the dimension of the array 
     * @return an int containing the array's dimension
     */
    int getDimension();
    
    /**
     * name of the array type
     */
    String getName();

    /**
     * full name of the array type
     */
    String getFullName();
    
    /**
     * full name of the array in alternative form, i.e.
     * e.g. <code>int[]</code> instead of <code>[I</code>
     */
    String getAlternativeNameRepresentation();
}