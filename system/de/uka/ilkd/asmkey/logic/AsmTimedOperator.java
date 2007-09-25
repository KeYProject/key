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

import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.asmkey.logic.sort.SortUtil;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator2;
import de.uka.ilkd.key.logic.sort.Sort;

/** This class extends the AsmOperator
 * for the explicit step extension of the logic
 *
 * @author Stanislas Nanchen 
 */

public class AsmTimedOperator extends AsmOp {

    /** [asm-rule]^t phi : modal 'box' operator with explicit step information */
    public static final Operator2 TBOX (Term step) {
	return new AsmTimedOperator ("TBox", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, null }, step) {
		public boolean validTopLevel(Term term) {
		    return super.validTopLevel(term)
			&& SortUtil.isPrimitiveSort(term.sub(1).sort());
		}
	    };
    }

    /** &lt;asm-rule&gt;^t phi : modal 'diamond' operator with explicit step information */
    public static final Operator2 TDIAMOND (Term step) {
        return new AsmTimedOperator("Diamond", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, null }, step) {
		public boolean validTopLevel(Term term) {
		    return super.validTopLevel(term)
			&& SortUtil.isPrimitiveSort(term.sub(1).sort());
		}
	    };
    }

    
    /** def^t(asm-rule) : modal operator with explicit step information */
    public static final Operator2 TDEF (Term step) {
	return new AsmTimedOperator("def", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE }, step);
    }

    /** upd^t(s <- f(x) in asm-rule) : modal operator with explicit step information. */
    public static final Operator2 TUPD (Term step) {
        return new AsmTimedOperator("upd", Sort.FORMULA, new Sort[] { null, null, PrimitiveSort.ASMRULE }, step) {
		public boolean validTopLevel(Term term) {
		    return super.validTopLevel(term)
			&& SortUtil.isPrimitiveSort(term.sub(0).sort())
			&& term.sub(0).sort() == term.sub(1).sort();
		}
	    };
    }

    /** Con^t(asm-rule) : modal operator with explicit step information */
    public static final Operator2 TCON(Term step) {
	return new AsmTimedOperator("Con", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE }, step);
    }
    
    /** inv^t(s in asm-rule) : modal operator with explicit step information */
    public static final Operator2 TINV(Term step) {
        return new AsmTimedOperator("inv", Sort.FORMULA, new Sort[] { null, PrimitiveSort.ASMRULE }, step) {
		public boolean validTopLevel(Term term) {
		    return super.validTopLevel(term)
			&& SortUtil.isPrimitiveSort(term.sub(0).sort());
		}
	    };
    }

    /** joinable^t(asm-rule and asm-rule) : modal operator with explicit step information */
    public static final Operator2 TJOINABLE(Term step) {
        return new AsmTimedOperator("joinable", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE }, step);
    }

    /** equi^t(asm-rule and asm-rule) : modal operator with explicit step information */
    public static final Operator2 TEQUI(Term step) {
        return new AsmTimedOperator("equi", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE }, step);
    }

    /** equiS^t(asm-rule and asm-rule) : modal operator with explicit step extension */
    public static final Operator2 TEQUIS(Term step) {
        return new AsmTimedOperator("equiS", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE }, step);
    }

    /** equiA^t(asm-rule and asm-rule) : modal operator with explicit step extension */
    public static final Operator2 TEQUIA(Term step) {
        return new AsmTimedOperator("equiA", Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE }, step);
    }

    /** accT^t(term in term) : modal operator with explicit step extension */
    public static final Operator2 TACCT(Term step) {
	return new AsmTimedOperator("accT", Sort.FORMULA, new Sort[] { null, null }, step);
    }

    /** accf^t(term in formula) : modal operator with explicit step extension */
    public static final Operator2 TACCF(Term step) {
	return new AsmTimedOperator("accF", Sort.FORMULA, new Sort[] { null, Sort.FORMULA }, step);
    }

    /** acc^t(term in asm-rule) : modal operator with explicit step extension */
    public static final Operator2 TACC(Term step) {
	return new AsmTimedOperator("acc", Sort.FORMULA, new Sort[] { null, PrimitiveSort.ASMRULE }, step);
    }


    private Term step;

    /** Main Contructor */
    AsmTimedOperator (String name, Sort sort, Sort[] args, boolean[] boundPositions, Term step) {
	super(new Name(name), sort, args, boundPositions);
	this.step = step;
    }

    AsmTimedOperator (String name, Sort sort, Sort[] args, Term step) {
	this(name, sort, args, null, step);
    }

    AsmTimedOperator (String name, Sort sort, Term step) {
	this(name, sort, null, null, step);
    }

}
