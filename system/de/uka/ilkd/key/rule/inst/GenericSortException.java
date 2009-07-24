// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.inst;

/** 
 * This exception thrown if there is no appropriate instantiation of
 * the generic sorts occurring within an "SVInstantiations"-object 
 */
public class GenericSortException extends SortException {

    /**
     * often used singleton
     */
    public static final GenericSortException UNINSTANTIATED_GENERIC_SORT =
        new GenericSortException("Generic sort is not yet instantiated");
    
    
    
    public GenericSortException(String description) {
	super(description);
    } 
}