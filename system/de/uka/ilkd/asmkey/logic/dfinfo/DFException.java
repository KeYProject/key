// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic.dfinfo;


/** Exception throwed in case of
 * problems in the dfinfo
 *
 * @author Stanislas Nanchen
 */

public class DFException extends Exception {
    
    public DFException(String msg) {
	super(msg);
    }
    
}
