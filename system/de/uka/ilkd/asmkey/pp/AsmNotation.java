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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.Notation;


/** This class contains the {@link de.uka.ilkd.key.pp.Notation}s for ASM terms and ASM rules. */

public final class AsmNotation {

    private AsmNotation() {}

    /** Notation for empty list */

    public static Notation empty_sequence() {
	return new Notation(100) {
		public void print(Term term, LogicPrinter sp) throws IOException {
		    AsmPrinter.printEmptySequence(sp);
		}
	    };
    }

    public static Notation sequence() {
	return new Notation(100) {
		public void print(Term term, LogicPrinter sp) throws IOException {
		    AsmPrinter.printSequence(sp, term);
		}
	    };
    }

    /** Notation for modality BOX. */
    public static Notation box() {
	return new Notation(60) {
		public void print(Term term, LogicPrinter sp) throws IOException {
		    AsmPrinter.printAsmModalityTerm(sp, "[[", "]]", term, 60);
		}
	    };
    }
    
    /** Notation for modality DIAMOND. */
    public static Notation diamond() {
	return new Notation(60) {
		public void print(Term term, LogicPrinter sp) throws IOException {
		    AsmPrinter.printAsmModalityTerm(sp, "<<", ">>", term, 60);
		}
	    };
    }
    
    
    /** Notation for sequential ASM program composition. */
    public static Notation seq() {
	return new Notation(0) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    AsmPrinter.printAsmSeq(sp, " seq ", term);
		}
	    };
    }
    
    /** Notation for parallel ASM program composition. */
    public static Notation par() {
	return new Notation(0) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    AsmPrinter.printAsmSeq(sp, " par ", term);
		}
	    };
    }
    
    /** Notation for ASM program SKIP. */
    public static Notation skip() {
	return new Notation.Constant("skip", 80);
    }
    
    /** Notation for ASM assignment rule. */
    public static Notation assign() {
	return new Notation.Infix(":=", 50, 60, 60);
    }
    
    /** Notation for ASM program construct IF-THEN-ELSE. */
    public static Notation if_() {
	return new Notation(0) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    AsmPrinter.printAsmIf(sp, term);
		}
		
	    };
    }
    
    /** Notation for ASM program construct ELSEIF */
    
    public static Notation elseif() {
	return new Notation(0) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    AsmPrinter.printAsmElseif(sp, term);
		}
	    };
    }
    
    /** Notation for ASM program construct LET-IN. */
    public static Notation let() {
	return new Notation(0) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    QuantifiableVariable v = term.varsBoundHere(1).getQuantifiableVariable(0);
		    AsmPrinter.printAsmLet(sp, v.toString(), term);
		}
		
	    };
    }
    
    /** Notation for ASM program construct FORALL-WITH-DO. */
    public static Notation forall() {
	return new Notation(0) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    QuantifiableVariable v = term.varsBoundHere(1).getQuantifiableVariable(0);
		    AsmPrinter.printAsmForAll(sp, v.toString(), term);
		}
		
	    };
    }
    
    /** Notation for ASM program construct TRY-ELSE. */
    public static Notation try_() {
	return new Notation(0) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    AsmPrinter.printAsmTry(sp, term);
		}
		
	    };
    }
    
    /** Notation for ASM named rules calls. */
    public static Notation named() {
	return new Notation(100) {
		public void print(Term term, LogicPrinter sp)
		    throws IOException {
		    AsmPrinter.printAsmNamedRule(sp, term);
		}
		
	    };
    }
    
    //    /** Notation for andalso */
    //     public static Notation andalso() {
    // 	return new Notation.Infix("&&", 50, 60, 50);
    //     }
    
    //     /** Notation for orelse */
    //     public static Notation orelse() {
    // 	return new Notation.Infix("||", 40, 50, 40);
    //     }
    
    /** Notation for timed */
    public static Notation timed() {
	return new Notation.Infix("^", 70, 80, 70);
    }
    
    /**
     * The standard concrete syntax for function and predicate terms.
     */
    static class Function extends Notation {
	
	public Function() {
	    super(100);
	}
	
	public void print(Term t,LogicPrinter sp)
	    throws IOException
	{
	    if(sp.getNotationInfo().getAbbrevMap().isEnabled(t)){
		sp.printTerm(t);
	    } else {
		AsmPrinter.printFunctionTerm(sp, t);
	    }
	}
    }
}
