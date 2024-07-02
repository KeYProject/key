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
   An entity of the program meta model.
   @author AL
   @author RN
 */
public interface ProgramModelElement 
    extends de.uka.ilkd.key.java.NamedModelElement {

    /**
       Returns the maximal expanded name including all applicable
       qualifiers.
       @return the full name of this program model element.
     */
    String getFullName();
    

}