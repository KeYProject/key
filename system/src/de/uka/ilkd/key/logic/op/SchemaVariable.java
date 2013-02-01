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


package de.uka.ilkd.key.logic.op;


/**
 * This interface represents the root of a schema variable hierarchy to be
 * express termstructures that match on logical terms. Schema variables
 * are used in Taclets where they act as placeholders for other
 * TermSymbols. The TermSymbols a SchemaVariable is allowed to match
 * is specified by their type and sort.
 */
public interface SchemaVariable extends ParsableVariable {
    
    /**
     * @return true if the schemavariable has the strict modifier which forces
     *         the instantiation to have exactly the same sort as the
     *         schemavariable (or if the sv is of generic sort - the
     *         instantiation of the generic sort)
     */
    boolean isStrict();
    
    /**
     * Creates a parseable string representation of the declaration of the 
     * schema variable.
     */
    String proofToString();
}
