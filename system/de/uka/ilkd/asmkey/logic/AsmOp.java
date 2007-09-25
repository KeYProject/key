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

import de.uka.ilkd.asmkey.logic.sort.EnumeratedSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * the standart implemention for the AsmOperator interface, with fixed
 * return sort. inherits from Function. 
 */
public class AsmOp extends Function implements AsmOperator {

    /** (result) sort of operator */
    private final Sort sort;

    /** argument sorts of operator. If the value at the ith position
     * is 'null', then the operator may accept a term of arbitrary
     * sort. */
    private final Sort[] args;

    /** if boundPositions[i] is true, then logical variables are bound
     * in the i-th subterm. */
    private final boolean[] boundPositions;

    /** Creates an operator without arguments (constant). @see
     * #AsmOperator(String, Sort, Sort[]) */
    AsmOp(Name name, Sort sort) {
        this(name, sort, null, null);
    }

    /** Creates an operator that doesn't bound variables. @see
     * #AsmOperator(String, Sort, Sort[], boolean[]) */
    AsmOp(Name name, Sort sort, Sort[] args) {
        this(name, sort, args, null);
    }

    /** Creates an asm operator.
     *
     * @param name name of operator
     * @param sort sort of term with this operator as top level operator
     * @param args count and sorts of arguments. If sort[i] is null,
     * the i-th argument of this operator may be of arbitrary sort.
     * @param boundPositions indices of subterms that bound variables.
     */
    AsmOp(Name name, Sort sort, Sort[] args, boolean[] boundPositions) {
	super(name, sort, args == null ? new Sort[0] : args);
        this.sort = sort;
        this.args = args;
        this.boundPositions = boundPositions;
    }

    public final Sort sort(Term[] term) {
	// HACK for metaderived
	if (sort == null) {
	    return term[0].sort();
	} else {
	    return sort;
	}
    }

    public boolean validTopLevel(Term term) {
        if (arity() != term.arity()) {
	    throw new IllegalArgumentException("The arities for operator " + name() +
					       "do not correspond: is " + term.arity() +
					       "should be " + arity());
        }
        if (args != null) {
            for (int i = 0; i < arity(); ++i) {
                if (args[i] != null) {
                    /* I don't know why there is an extra check for
                     * schema variables, but 'Function.validTopLevel'
                     * does it also, -hs. */
                    if (term.sub(i).op() instanceof SchemaVariable ||
			term.sub(i).op() instanceof NArityLogicVariable) {
                        // nothing
                    } else if (!term.sub(i).sort().extendsTrans(args[i])) {
			throw new IllegalArgumentException
			    ("The sort of the " + i + "-th argument for the operator " + name()
			     + " is not compatible: sort provided=" + term.sub(i).sort() +
			     ";sort expected=" + args[i] + ".");
                    }
                }
            }
        }
        return true;
    }

    public final boolean boundVariables(int index) {
        return boundPositions != null && boundPositions[index];
    }

    public Term createTerm(ArrayOfQuantifiableVariable vars, Term[] terms) {
	return AsmUtil.createTerm(this, vars, terms);
    }

    /** for debug only */
    public String toString() {
        return "[AsmOp:name=" + name() + ",sort=" + sort + "]";
    }

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and may not be changed by modalities
     */
    public boolean isRigid (Term term) {
	// TODO
 	return false;
    }

    /* --- static part ---*/

    /** to ease the creation of binary boolean operators */
    public static AsmOperator createBooleanBinaryOperator(Name name) {
	return new AsmOp(name, EnumeratedSort.BOOLEAN,
			 new Sort[] { EnumeratedSort.BOOLEAN , EnumeratedSort.BOOLEAN });
    }

}
