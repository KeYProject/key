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
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

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
    public ImmutableArray<QuantifiableVariable> boundVars;

    /** 
     * the Term
     */
    public Term term;

    /** creates a term with (possibly) bound variables
     * @param vars the variables that are bound in t
     * @param t the term
     */
    public TermWithBoundVars(ImmutableArray<QuantifiableVariable> vars, Term t) {
	boundVars = vars;
	term = t;
    }
    
}









