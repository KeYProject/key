// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;


import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Operator;


/** Utility class to perform substitution of formal parameters in
 * named ASM rules. */

final class FormalParameterSubstitution {

    private FormalParameterSubstitution() {}

    /** Short refernce to TermFactory. */
    private static final TermFactory tf = TermFactory.DEFAULT;


    /** This method applies the substitution given in 'map' on
     * term. 'map' contains entries from 'FormalParameter' to 'Term'.
     * The substitution is easy because formal parameters may not be
     * bound. */
    protected static Term apply(Map map, Term term) {
        Operator op = term.op();
        if (map.containsKey(op)) {
            return (Term) map.get(op);
        } else {
            boolean changed = false;
            Term[] terms = new Term[term.arity()];
            ArrayOfQuantifiableVariable[] boundVars = new ArrayOfQuantifiableVariable[term.arity()];
            for (int i = 0; i < terms.length; ++i) {
                Term sub = term.sub(i);
                terms[i] = apply(map, sub);
                if (terms[i] != sub) {
                    changed = true;
                }
                boundVars[i] = term.varsBoundHere(i);
            }
            if (changed) {
                return tf.createTerm(op, terms, boundVars, term.javaBlock());
            } else {
                return term;
            }
        }
    }

}
