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

import de.uka.ilkd.asmkey.logic.dfinfo.DFInfo;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.NonRigidFunction;

/** Utility class with static methods for ASM rules. */

public final class AsmUtil {

    private AsmUtil() {}

    /** Determines if a given term is 'pure', that means it doens't
     * contain a model operator. */
    public static boolean isPure(Term term) {
        if (term instanceof AsmTerm) {
            return false;
        }
        for (int i = 0; i < term.arity(); ++i) {
            if (!isPure(term.sub(i))) {
                return false;
            }
        }
        return true;
    }


    /** Determines if a given term is 'static', that means it is pure
     * and doens't contain a dynamic funtion. */
    public static boolean isStatic(Term term) {
        if (term instanceof AsmTerm || term.op() instanceof NonRigidFunction) {
            // TODO: How should predicate symbols be handled? Are they
            // always rigid?
            return false;
        }
        for (int i = 0; i < term.arity(); ++i) {
            if (!isStatic(term.sub(i))) {
                return false;
            }
        }
        return true;
    }

    /** Determines if a given semisequent is 'static', that means itn formulas are pure
     * and don't contain a dynamic funtion. */

    public static boolean isStatic(Semisequent seq) {
	IteratorOfConstrainedFormula it = seq.iterator();
	ConstrainedFormula form;

	while (it.hasNext()) {
	    form = it.next();
	    if (!isStatic(form.formula())) { return false; }
	}
	
	return true;
    }

    /** Determines if an AsmRule can or not update a location. This information is obtained
     * by the static analysis.
     */
    public static boolean mayUpdate(UpdateDFInfoContainer rule, Term t) {
	DFInfo updateInfo = rule.getUpdateDFInfo();

	Name function = t.op().name();

	return updateInfo.containsName(function);
    }

    /** determines if an AsmTerm can or not access a location. This information is obtained
     * by the static analysis.
     */
    public static boolean mayAccess(AccessDFInfoContainer term, Term t) {
	DFInfo accessInfo = term.getAccessDFInfo();
	Name function = t.op().name();
	return accessInfo.containsName(function);
    }

    /* -- for the creation of AsmOpertor terms -- */

    
    public static Term createTerm(AsmOperator op,
				  ArrayOfQuantifiableVariable vars, Term[] terms) {
        
	Term result;

	checkArgs(op, vars, terms);

	result = new AsmTerm(op, terms, vars);
        if (!op.validTopLevel(result)) {
            throw new IllegalArgumentException("Term not valid with operator: " + op.name());
        }
        return result;
    }

    public static Term createProgramTerm(AsmOperator op,
					 ArrayOfQuantifiableVariable vars, Term[] terms) {
        
	Term result;

	checkArgs(op, vars, terms);

	result = new AsmProgram(op, terms, vars);
        if (!op.validTopLevel(result)) {
            throw new IllegalArgumentException("Term not valid with operator: " + op.name());
        }
        return result;
    }

    private static void checkArgs(AsmOperator op,
				  ArrayOfQuantifiableVariable vars, Term[] terms) {
	/* create a new term with the given bound variables and subterms. */
        if (terms != null) {
            for (int i = 0; i < terms.length; ++i) {
                if (terms[i] == null) {
                    throw new IllegalArgumentException("terms[" + i + "] may not be null.");
                }
            }
        }
        if (op.arity() == 0) {
            if (!(vars == null || vars.size() == 0)) {
                throw new IllegalArgumentException("Operator " + op.name() +
						   " can not have bound variables.");
            }
            if (terms != null && terms.length != 0) {
                throw new IllegalArgumentException("Invalid number of subterms.");
            }
        } else {
            if (terms == null || terms.length != op.arity()) {
                throw new IllegalArgumentException
		    ("Arity("+ op.arity() +") of operator " + op.name() +
		     " does not match: " + terms.length + " terms provided");
            }
            boolean bound = false;
            for (int i = 0; i < terms.length; ++i) {
                if (op.boundVariables(i)) {
                    bound = true;
                    break;
                }
            }
            if (bound == (vars == null || vars.size() == 0)) {
                throw new IllegalArgumentException
		    ("Operator " + op.name() + " does not match with bound variables.");
            }
        }
    }
}

