// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

package de.uka.ilkd.key.logic.sort;


public interface ClassInstanceSort extends ObjectSort {

    /** 
     * returns true if this sort represents a java abstract class
     * or interface
     */
    boolean representAbstractClassOrInterface();
}
