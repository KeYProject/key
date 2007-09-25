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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;

/** Term implementation for ASM rules and ASM dynamic logic
 * formulas/terms.
 *
 * @author Stanislas Nanchen
 * @author Hubert Schmid
 */

class AsmTerm extends Term {

    private static final Term[] EMPTY_TERMS = new Term[] {};

    /** top level operator */
    private final AsmOperator op;

    /** subterms, may be null if this term has no subterms. */
    private final Term[] terms;

    /** variables bound by top level operator of this term. */
    private final ArrayOfQuantifiableVariable boundVariables;

    /** depth of term. (chached value) */
    private int depth;


    /** create term with given top level operator and no subterms. */
    AsmTerm(AsmOperator op) {
        this(op, EMPTY_TERMS, null);
    }

    /** create term with given top level operator and given subterms
     * and no bound variables. */
    AsmTerm(AsmOperator op, Term[] terms) {
        this(op, terms, null);
    }

    /** create term with given top level operator, given subterms,
     * bound variables. */
    AsmTerm(AsmOperator op, Term[] terms, ArrayOfQuantifiableVariable vars) {
        super(op, op.sort(terms));
        if (terms == null) {
            throw new IllegalArgumentException("terms may not be null");
        } else {
            for (int i = 0; i < terms.length; ++i) {
                if (terms[i] == null) {
                    throw new IllegalArgumentException("term may not be null");
                }
            }
        }
        this.op = op;
        this.terms = terms;
	// HACK: sn, horrible hack, better to check we have a set.
	if (op == AsmProgramOperator.FORALL) {
	    this.boundVariables =
		new ArrayOfQuantifiableVariable(vars.getQuantifiableVariable(0));
	} else {
	    this.boundVariables = vars;
	}

	fillCaches();
    }

    /* --- methods --- */

    public int arity() {
        return terms.length;
    }

    public Term sub(int index) {
	Term term = terms[index];
        return term;
    }

    public int depth() {
        return depth;
    }

    public ArrayOfQuantifiableVariable varsBoundHere(int index) {
        if (op.boundVariables(index)) {
            return boundVariables;
        } else {
            return EMPTY_VAR_LIST;
        }
    }

    protected void fillCaches() {
	super.fillCaches();
	depth = TermUtil.maxDepth(terms, -1) + 1;
    }
    
}
