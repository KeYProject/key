// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.asmkey.logic.sort.EnumeratedSort;
import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Operator2;
import de.uka.ilkd.key.logic.sort.Sort;
//import de.uka.ilkd.asmkey.logic.CollectionSort;

/** This class extends the AsmOperator class for the asm rule
 * operators to handle the label mechanisms.
 *
 * @author Stanislas Nanchen 
 */
public class AsmProgramOperator extends AsmOp {

     /* ASMs */

    /** operator for sequential composition of asm rules. */
    public static final Operator2 SEQ =
        new AsmProgramOperator("seq", new Sort[] { PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE });

    /** operator for parallel composition of asm rules. */
    public static final Operator2 PAR =
        new AsmProgramOperator("par", new Sort[] { PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE });

    /** operator for asm skip rule. */
    public static final Operator2 SKIP = new AsmProgramOperator("skip");

    /** operator for asm assignment rule. */
    public static final Operator2 ASSIGN = new AsmProgramOperator("assign",
							   new Sort[] { null, null }) {
            public boolean validTopLevel(Term term) {
                return super.validTopLevel(term)
                    //&& SortUtil.isPrimitiveSort(term.sub(0).sort())
		    && ((term.sub(0).sort() == AbstractMetaOperator.METASORT) ||
			(term.sub(1).sort() == AbstractMetaOperator.METASORT) ||
			(term.sub(0).sort() == term.sub(1).sort()));
            }
        };

    /** operator for asm if rule. */
    public static final Operator2 IF =
        new AsmProgramOperator("if",
			new Sort[] { EnumeratedSort.BOOLEAN, PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE });

    /** operator for asm elseif rule. */
    public static final Operator2 ELSEIF =
        new AsmProgramOperator("elseif",
			new Sort[] { EnumeratedSort.BOOLEAN, PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE});
    
    /** operator for asm let rule. */
    public static final Operator2 LET =
        new AsmProgramOperator(
                        "let",
                        new Sort[] { null, PrimitiveSort.ASMRULE },
                        new boolean[] { false, true }) {
            public boolean validTopLevel(Term term) {
                return super.validTopLevel(term);
                    //&& SortUtil.isPrimitiveSort(term.sub(0).sort());
            }
        };

    /** operator for asm forall rule. */
    public static final Operator2 FORALL =
        new AsmProgramOperator(
                        "forall",
                        new Sort[] { EnumeratedSort.BOOLEAN, PrimitiveSort.ASMRULE },
                        new boolean[] { true, true });

    /** operator for asm try rule. */
    public static final Operator2 TRY =
        new AsmProgramOperator("try",
			new Sort[] { PrimitiveSort.ASMRULE, PrimitiveSort.ASMRULE });

    /* static analyis */
    
    public static final Operator2 PROC =
	new AsmProgramOperator("proc",
			new Sort[] { PrimitiveSort.ASMRULE });


    /** Creates an operator without arguments (constant). @see
     * #AsmProgramOperator(String, Sort[]) */
    AsmProgramOperator(String name) {
        this(name, null, null);
    }

    /** Creates an operator that doesn't bound variables. @see
     * #AsmProgramOperator(String, Sort[], boolean[]) */
    AsmProgramOperator(String name, Sort[] args) {
        this(name, args, null);
    }

    /** Creates an asm rule operator. the returned sort is always
     * PrimitiveSort.ASMRULE.
     *
     * @param name name of operator
     * @param args count and sorts of arguments. If sort[i] is null,
     * the i-th argument of this operator may be of arbitrary sort.
     * @param boundPositions indices of subterms that bound variables.
     */
    AsmProgramOperator(String name, Sort[] args, boolean[] boundPositions) {
	super(new Name(name), PrimitiveSort.ASMRULE, args, boundPositions);
    }

    public final Term createTerm(ArrayOfQuantifiableVariable vars, Term[] terms) {
	return AsmUtil.createProgramTerm(this, vars, terms);
    }

    /** for debug only */
    public String toString() {
        return "[AsmProgramOperator:name=" + name() + "]";
    }

}
