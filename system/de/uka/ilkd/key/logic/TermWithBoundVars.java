// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;

/**
 * A TermWithBoundVars is an object that contains a Term and 0, 1,
 * or 2 QuantifiableVariable that are bound in the Term.
 * This class is needed for OCL simplification when parsing the 
 * arguments of an OCL Collection operation.
 */
public class TermWithBoundVars {

    /** 
     * the variables that are bound in the Term
     */
    public ArrayOfQuantifiableVariable boundVars;

    /** 
     * the Term
     */
    public Term term;

    /** creates a term with (possibly) bound variables
     * @param vars the variables that are bound in t
     * @param t the term
     */
    public TermWithBoundVars(ArrayOfQuantifiableVariable vars, Term t) {
	boundVars = vars;
	term = t;
    }
    
}









