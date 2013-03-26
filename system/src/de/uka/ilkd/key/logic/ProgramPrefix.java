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


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.NonTerminalProgramElement;

/**
 * this interface is implemented by program elements that may be matched
 * by the inactive program prefix
 */
public interface ProgramPrefix extends NonTerminalProgramElement {
    
    /** returns the number of prefix starting with this element
     * @return the number of prefix starting with this element
     */ 
    int getPrefixLength();
    
    /** returns the i-th prefix element */
    ProgramPrefix getPrefixElementAt(int i);
    
    /** returns an array with all prefix elements starting at 
     * this element */
    ImmutableArray<ProgramPrefix> getPrefixElements();
    
    /** returns the position of the first active child */
    PosInProgram getFirstActiveChildPos();
        
}
