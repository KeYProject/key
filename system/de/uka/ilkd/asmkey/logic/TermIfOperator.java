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
import de.uka.ilkd.asmkey.logic.sort.GenericSort;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;

public class TermIfOperator implements AsmOperator {

    public static final TermIfOperator OPERATOR = new TermIfOperator();
    
    private static final GenericSort SORT = new GenericSort(new Name("term if"));

    private Name name;

    private TermIfOperator() {
	this.name = new Name("term if");
    }

    public Name name() {
	return name;
    }

    public boolean validTopLevel(Term term) {
	/* to have a valid top level:
	 * - arities must be the same
	 * - the sort of the first subterm is boolean
	 * - the sort of the 2nd and 3nd term are the same.
	 */
	if(arity() == term.arity() &&
	   term.sub(0).sort() == EnumeratedSort.BOOLEAN &&
	   term.sub(1).sort() == term.sub(2).sort()) {
	    return true;
	} else {
	    return false;
	}
    }

    public Sort sort(Term[] term) {
	/* the sort of the if operator is the sort
	 * of the 2nd (and 3rd term)
	 */
	return term[1].sort();
    }

    public int arity() {
	return 3;
    }

    public boolean isRigid (Term term) {
	return term.hasRigidSubterms();
    }
    
    public boolean boundVariables(int index) {
	return false;
    }

    /** 
     * implements the default operator matching rule which means that
     * the compared object have to be equal otherwise matching
     * fails. Taken from {@link de.uka.ilkd.key.logic.op.TermSymbol}
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        if (subst == this) {
            return mc;
        }
        Debug.out("Operators are different(template, candidate)", this, subst);
        return null;
    }

    /** 
     * @param vars all quantified variables. The operator should now
     * how to handle this. In most cases, the array will be empty.
     * @param terms the subterms
     * @return a term with this operator as top level operator and the
     * given subterms */
    public Term createTerm(ArrayOfQuantifiableVariable vars, Term[] terms) {
	return AsmUtil.createTerm(this, vars, terms);
    }

    public Sort argSort(int i) {
	if (i==0) {
	    return EnumeratedSort.BOOLEAN;
	} else {
	    return SORT;
	}
    }

}
