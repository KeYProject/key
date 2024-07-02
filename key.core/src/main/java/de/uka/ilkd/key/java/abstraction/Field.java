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

import de.uka.ilkd.key.logic.op.IProgramVariable;

/**
   A program model element representing fields.
   @author AL
   @author RN
   The file has been modified by the KeY team.   
 */
public interface Field extends Variable, Member {

    /** 
     * returns the program variable associated with this field 
     * @return the program variable associated with this field 
     */
    IProgramVariable getProgramVariable();

    /**
     * returns the name of the field as used in programs. In the logic
     * each field has a unique name which is composed by the class name where 
     * it is declared and its source code name 
     *
     * @return returns the name of the field as used in programs
     */
    String getProgramName();

}