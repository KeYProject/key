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

package de.uka.ilkd.key.java.abstraction;

/**
   A program model element representing variables.
   @author AL
   @author RN
 */
public interface Variable extends ProgramModelElement {
    
    /**
       Checks if this variable is final.
       @return <CODE>true</CODE> if this variable is final,
       <CODE>false</CODE> otherwise.
     */
    boolean isFinal();

    /**
       Returns the type of this variable.
       @return the type of this variable.
    */
    Type getType();
}