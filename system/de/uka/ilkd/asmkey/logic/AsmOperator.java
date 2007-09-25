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
import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.asmkey.logic.sort.SortUtil;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator2;
import de.uka.ilkd.key.logic.sort.Sort;


/** This interface extends the interface Operator2 and contains static
 * fields for many ASM operators. It serves as base Interface for
 * all operators defined for AsmKeY.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen 
 */
public interface AsmOperator extends Operator2 {

    /* --- necessary boolean operators --- */

    /** boolean operator for 'and' */
    public static final AsmOperator TERM_AND =
	AsmOp.createBooleanBinaryOperator(new Name("and"));	

    /** boolean operator for 'and also' */
    public static final AsmOperator TERM_ANDALSO = 
	AsmOp.createBooleanBinaryOperator(new Name("and also"));
    
    /** boolean operator for 'or' */
    public static final AsmOperator TERM_OR = 
	AsmOp.createBooleanBinaryOperator(new Name("or"));

    /** boolean operator for 'or else' */
    public static final AsmOperator TERM_ORELSE =
	AsmOp.createBooleanBinaryOperator(new Name("or else"));

    /** boolean opertor for '==' */
    public static final AsmOperator TERM_EQUALS =
	new AsmOp(new Name("=="), EnumeratedSort.BOOLEAN, new Sort[] { null, null }) {
	    public boolean validTopLevel(Term term) {
		return super.validTopLevel(term)
		    && term.sub(0).sort() == term.sub(1).sort();
	    }
	};

    /** modal operator for '[asm-rule] phi'. */
    public static final AsmOperator BOX =
        new AsmOp(new Name("Box"), Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, Sort.FORMULA }) {
            public boolean validTopLevel(Term term) {
                return super.validTopLevel(term)
                    && SortUtil.isPrimitiveSort(term.sub(1).sort());
            }
        };

    /** modal operator for '&lt;asm-rule&gt; phi'. */
    public static final AsmOperator DIAMOND =
        new AsmOp(new Name("Diamond"), Sort.FORMULA, new Sort[] { PrimitiveSort.ASMRULE, Sort.FORMULA }) {
            public boolean validTopLevel(Term term) {
                return super.validTopLevel(term)
                    && SortUtil.isPrimitiveSort(term.sub(1).sort());
            }
        };

    /* --- supplementary interface method, for AsmTerm */

    boolean boundVariables(int index);

    Sort argSort(int i);

    /**
     * To check wether a term with this operator as top-level
     * is valid. generic sort are as in ML and the hashmap contains
     * the contraints that a now valid.
     */
    //boolean validTopLevel(Term term, HashMapFromGenericSortToAsmSort sort_constraint); 

}

