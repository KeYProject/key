// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.util.graph;

/**
 * This exception is raised if one attemps
 * to insert an edge that would cause a cycle
 * to appear.
 */
public class CycleException extends Exception {

    public CycleException(String message) {
	super(message);
    }

}
