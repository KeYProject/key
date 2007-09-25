// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.pp;

import java.io.IOException;

import de.uka.ilkd.asmkey.logic.AsmProgramOperator;
import de.uka.ilkd.asmkey.logic.SortDependingAsmOperator;
import de.uka.ilkd.asmkey.logic.TermUtil;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.pp.AbstractAsmPrinter;
import de.uka.ilkd.key.pp.LogicPrinter;


/** LogicPrinter for ASM terms and ASM rules. This class contains the actual
 * code to print the ASM terms and rules. The methods are called from the ASM notations
 * ({@link de.uka.ilkd.asmkey.pp.AsmNotation}).
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen */

final class AsmPrinter extends AbstractAsmPrinter {

        /** Indentation level for if, try and joinable. */
        private static final int INDENT = 2;

    protected static void printEmptySequence(LogicPrinter sp) throws IOException {
	startTerm(sp,1);
	layouter(sp).beginC(0).print(":<>");
	layouter(sp).end();
    }

    protected static void printSequence(LogicPrinter sp, Term seq) throws IOException {
	startTerm(sp, 2);
	layouter(sp).beginC(1).print("'<");
	markStartSub(sp);
	sp.printTerm(seq.sub(0));
	markEndSub(sp);
	print_seq(sp, seq.sub(1));
	layouter(sp).print(">").brk(1, 2);
	layouter(sp).end();
    }

    private static void print_seq(LogicPrinter sp, Term seq) throws IOException {
	if ( seq.op() instanceof SortDependingAsmOperator &&
	     seq.op().name().toString().substring(0,4).compareTo("cons") == 0) {
	    markStartSub(sp);
	    startTerm(sp, 2);
	    layouter(sp).print(",");
	    markStartSub(sp);
	    sp.printTerm(seq.sub(0));
	    markEndSub(sp);
	    print_seq(sp, seq.sub(1));
	    markEndSub(sp);
	} else {
	    // end of explicit enumeration
	    if ( seq.op() instanceof SortDependingAsmOperator &&
		 seq.op().name().toString().substring(0,3).compareTo("nil") == 0) {
		// end of list
	    } else {
		// tail of list
		layouter(sp).brk(0,2).print(":");
		markStartSub(sp);
		sp.printTerm(seq);
		markEndSub(sp);
	    }
	}
    } 

        /** Used for DL modalities BOX and DIAMOND. */
        protected static void printAsmModalityTerm(
                LogicPrinter sp,
                String left,
                String right,
                Term phi,
                int ass)
                throws IOException {
                startTerm(sp, 2);
                layouter(sp).beginC(0).print(left);
                markStartSub(sp);
                sp.printTerm(phi.sub(0));
                markEndSub(sp);
                layouter(sp).print(right).brk(1, 2);
                maybeParens(sp, phi.sub(1), ass);
                layouter(sp).end();
        }

    /** Used for sequential and parallel program composition. */
    protected static void printAsmSeq(LogicPrinter sp, String separator, Term phi)
	throws  IOException {
	startTerm(sp, 2);
	layouter(sp).beginC(0);
	markStartSub(sp);
	sp.printTerm(phi.sub(0));
	markEndSub(sp);
	layouter(sp).print(separator).brk();
	markStartSub(sp);
	sp.printTerm(phi.sub(1));
	markEndSub(sp);
	layouter(sp).end();
    }

    /** Used for ASM if program construct. */
    protected static void printAsmIf(LogicPrinter sp, Term phi)
	throws  IOException {
	print_if_start(sp, phi, "if ");
    }

    protected static void printAsmElseif(LogicPrinter sp, Term phi)
	throws IOException {
	print_if_start(sp, phi, "elseif ");
    }

    private static void print_if_start(LogicPrinter sp, Term phi, String if_)
	throws IOException {
	startTerm(sp, 4);
	layouter(sp).beginC(AsmPrinter.INDENT).print(if_);
	markStartSub(sp);
	sp.printTerm(phi.sub(0));
	markEndSub(sp);
	layouter(sp).print(" then").brk();
	markStartSub(sp);
	sp.printTerm(phi.sub(1));
	markEndSub(sp);
	print_elseif(sp, phi.sub(2));
	
	layouter(sp).brk(1, -AsmPrinter.INDENT).print("end").end();
    }

    private static void print_elseif(LogicPrinter sp, Term phi) 
	throws IOException {
	if (phi.op() == AsmProgramOperator.ELSEIF) {
	    markStartSub(sp);
	    startTerm(sp,4);
	    layouter(sp).brk(1, -AsmPrinter.INDENT).print("elseif ");
	    markStartSub(sp);
	    sp.printTerm(phi.sub(0));
	    markEndSub(sp);
	    layouter(sp).print(" then").brk();
	    markStartSub(sp);
	    sp.printTerm(phi.sub(1));
	    markEndSub(sp);
	    print_elseif(sp, phi.sub(2));
	    markEndSub(sp);
	} else {
	    layouter(sp).brk(1, -AsmPrinter.INDENT).print("else").brk();
	    markStartSub(sp);
	    sp.printTerm(phi);
	    markEndSub(sp);
	}
    }

        /** Used for ASM try program construct. */
        protected static void printAsmTry(LogicPrinter sp, Term phi)
                throws  IOException {
                startTerm(sp, 3);
                layouter(sp).beginC(AsmPrinter.INDENT).print("try").brk();
                markStartSub(sp);
                sp.printTerm(phi.sub(0));
                markEndSub(sp);
                layouter(sp).brk(1, -AsmPrinter.INDENT).print("else").brk();
                markStartSub(sp);
                sp.printTerm(phi.sub(1));
                markEndSub(sp);
                layouter(sp).brk(1, -AsmPrinter.INDENT).print("end").end();
        }

        /** Used for ASM let program construct. */
        protected static void printAsmLet(LogicPrinter sp, String var, Term phi)
                throws  IOException {
                startTerm(sp, 2);
                layouter(sp).beginC(2).print("let " + var + " = ");
                markStartSub(sp);
                sp.printTerm(phi.sub(0));
                markEndSub(sp);
                layouter(sp).print(" in").brk();
                markStartSub(sp);
                sp.printTerm(phi.sub(1));
                markEndSub(sp);
                layouter(sp).brk().print("end").end();
        }

        /** Used for ASM forall program construct. */
        protected static void printAsmForAll(LogicPrinter sp, String var, Term phi)
                throws  IOException {
                startTerm(sp, 2);
                layouter(sp).beginC(2).print("forall " + var + " with ");
                markStartSub(sp);
                sp.printTerm(phi.sub(0));
                markEndSub(sp);
                layouter(sp).print(" do").brk();
                markStartSub(sp);
                sp.printTerm(phi.sub(1));
                markEndSub(sp);
                layouter(sp).brk().print("end").end();
        }

        /** Print ASM named rule calls. */
        protected static void printAsmNamedRule(LogicPrinter sp, Term t)
        throws IOException {
                startTerm(sp, t.arity());
                if (t.arity() > 0) {
                        layouter(sp).print("(").beginC(0);
                        for (int i = 0; i < t.arity(); ++i) {
                                markStartSub(sp);
                                sp.printTerm(t.sub(i));
                                markEndSub(sp);

                                if (i < t.arity() - 1) {
                                        layouter(sp).print(",").brk(1, 0);
                                }
                        }
                        layouter(sp).print(")").end();
                }
        }


    protected static void printFunctionTerm(LogicPrinter sp, Term t)
    throws IOException {
	startTerm(sp, t.arity());
	layouter(sp).print(t.op().name().toString());
	if(t.arity()>0) {
	    int asm = TermUtil.firstNonAsmSortIndex((Function)t.op());
	    if (0 < asm) {
		layouter(sp).print("(:").beginC(0);
	    } else {
		layouter(sp).print("(").beginC(0);
	    }
	    for (int i=0;i<t.arity();i++) {
		markStartSub(sp);		
		sp.printTerm(t.sub(i));
		markEndSub(sp);
		
		if (i == asm-1 && i != t.arity()-1) {
		    layouter(sp).print(";").brk(1,0);
		} else {
		    if (i<t.arity()-1) {
			layouter(sp).print(",").brk(1,0);
		    }
		}
	    }
	    if (asm == t.arity()) {
		layouter(sp).print(";)").end();
	    } else {
		layouter(sp).print(")").end();
	    }
	}
    }
}
