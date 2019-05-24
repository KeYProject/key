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

package de.uka.ilkd.key.logic;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.java.statement.MethodFrame;

/**
 * this interface is implemented by program elements that may be matched
 * by the inactive program prefix
 */
public interface ProgramPrefix extends NonTerminalProgramElement {
    
    /** return true if there is a next prefix element */
    boolean hasNextPrefixElement();    

    /** return the next prefix element 
     * if no next prefix element is available an IndexOutOfBoundsException is thrown
     */
    ProgramPrefix getNextPrefixElement();    

    /** return the last prefix element */
    ProgramPrefix getLastPrefixElement();    
    
    /** returns an array with all prefix elements starting at 
     * this element */
    ImmutableArray<ProgramPrefix> getPrefixElements();
    
    /** returns the position of the first active child */
    PosInProgram getFirstActiveChildPos();
    
    /** returns the length of the prefix */
    int getPrefixLength();
    
    /** returns the inner most {@link MethodFrame} */
    MethodFrame getInnerMostMethodFrame();

}