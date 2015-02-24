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

import de.uka.ilkd.key.java.expression.Literal;

/**
   A program model element representing types.
   @author AL
   @author RN
 */
public interface Type extends ProgramModelElement {

    /** 
     * returns the default value of the given type 
     * according to JLS Sect. 4.5.5
     * @return the default value of the given type 
     * according to JLS Sect. 4.5.5
     */
    Literal getDefaultValue();

}