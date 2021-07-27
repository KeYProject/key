// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.pp;

import java.io.IOException;
import java.util.Iterator;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

/**
 * Encapsulate the concrete syntax used to print a term. The {@link
 * NotationInfo} class associates a Notation with every {@link
 * de.uka.ilkd.key.logic.op.Operator}. The various inner classes of this class
 * represent different kinds of concrete syntax, like prefix, infix, postfix,
 * function style, attribute style, etc.
 */
public abstract class Notation {

    /**
     * The priority of this operator in the given concrete syntax. This is
     * used to determine whether parentheses are required around a subterm.
     */
    private final int priority;

    /** Create a Notation with a given priority. */
    protected Notation(int priority) {
	this.priority = priority;
    }

    /** get the priority of the term */
    public final int getPriority() {
	return priority;
    }

    /**
     * Print a term to a {@link LogicPrinter}. Concrete subclasses override
     * this to call one of the <code>printXYZTerm</code> of
     * {@link LogicPrinter}, which do the layout.
     */
    public abstract void print(Term t, LogicPrinter sp) throws IOException;

    /**
     * Print a term without beginning a new block. See
     * {@link LogicPrinter#printTermContinuingBlock(Term)}for the idea
     * behind this. The standard implementation just delegates to
     * {@link #print(Term,LogicPrinter)}
     */
    public void printContinuingBlock(Term t, LogicPrinter sp)
	    throws IOException {
	print(t, sp);
    }

    
    
    /**
     * The standard concrete syntax for constants like true and false.
     */
    public static final class Constant extends Notation {
	private final String name;

	public Constant(String name, int prio) {
	    super(prio);
	    this.name = name;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printConstant(t, name);
	}
    }

    /**
     * The standard concrete syntax for prefix operators.
     */
    public static final class Prefix extends Notation {
	private final String name;
	private final int ass;

	public Prefix(String name, int prio, int ass) {
	    super(prio);
	    this.name = name;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printPrefixTerm(name, t, t.sub(0), ass);
	}

    }

    /**
     * The standard concrete syntax for infix operators.
     */
    public static final class Infix extends Notation {
	private final String name;
	private final int assLeft, assRight;

	public Infix(String name, int prio, int assLeft, int assRight) {
	    super(prio);
	    this.name = name;
	    this.assLeft = assLeft;
	    this.assRight = assRight;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printInfixTerm(t.sub(0), assLeft, name, t, t.sub(1), assRight);
	}

	/**
         * Print a term without beginning a new block. This calls the
         * {@link LogicPrinter#printTermContinuingBlock(Term)} method.
         */
	public void printContinuingBlock(Term t, LogicPrinter sp)
		throws IOException {
	    sp.printInfixTermContinuingBlock(t.sub(0), assLeft, name, t, t.sub(1), assRight);
	}

    }
    

    public static final class LabelNotation extends Notation {
        
        private final String left;
        private final String right;
        
        public LabelNotation(String beginLabel, String endLabel, int prio) {
            super(prio);
            left = beginLabel;
            right = endLabel;
        }
        
        public void print(Term t, LogicPrinter sp) throws IOException {
            sp.printLabels(t, left, right);
        }
    }
    
    /**
     * The standard concrete syntax for quantifiers.
     */
    public static final class Quantifier extends Notation {
	private final String name;
	private final int ass;

	public Quantifier(String name, int prio, int ass) {
	    super(prio);
	    this.name = name;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printQuantifierTerm(name, t.varsBoundHere(0), t.sub(0), ass);
	}

    }
    

    /**
     * The standard concrete syntax for DL modalities box and diamond.
     */
    public static final class ModalityNotation extends Notation {
	private final String left, right;

	private final int ass;

	public ModalityNotation(String left, String right, int prio, int ass) {
	    super(prio);
	    this.left = left;
	    this.right = right;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    assert t.op() instanceof Modality;
	    assert t.javaBlock() != null;
	    sp.printModalityTerm(left, t.javaBlock(), right, t, ass);
	}
    }
    

    /**
     * The concrete syntax for DL modalities represented with a
     * SchemaVariable.
     */
    public static final class ModalSVNotation extends Notation {
	private final int ass;

	public ModalSVNotation(int prio, int ass) {
	    super(prio);
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printModalityTerm("\\modality{" + t.op().name().toString()
			+ "}", t.javaBlock(), "\\endmodality", t, ass);
	}
    }

    
    /**
     * The standard concrete syntax for update application.
     */
    public static final class UpdateApplicationNotation extends Notation {

	public UpdateApplicationNotation() {
	    super(115);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    assert t.op() == UpdateApplication.UPDATE_APPLICATION;
	    final Operator targetOp = UpdateApplication.getTarget(t).op();
	    final int assTarget 
	    = (t.sort() == Sort.FORMULA 
		    ? (targetOp.arity() == 1 ? 60 : 85) 
			    : 110);

	    sp.printUpdateApplicationTerm("{", "}", t, assTarget);
	}
    }
    
    
    /**
     * The standard concrete syntax for elementary updates.
     */
    public static final class ElementaryUpdateNotation extends Notation {

	public ElementaryUpdateNotation() {
	    super(150);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printElementaryUpdate(":=", t, 0);
	}
    }    
    
    
    /**
     * The standard concrete syntax for parallel updates 
     */
    public static final class ParallelUpdateNotation extends Notation {

	public ParallelUpdateNotation() {
	    super(100);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    assert t.op() == UpdateJunctor.PARALLEL_UPDATE;
	    
	    sp.printParallelUpdate("||", t, 10);
	}
    }    
    
    
    /**
      * The standard concrete syntax for substitution terms.
      */
    public static final class Subst extends Notation {
	public Subst() {
	    super(120);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    QuantifiableVariable v = instQV(t, sp, 1);
	    final int assTarget = (t.sort() == Sort.FORMULA ? (t.sub(1)
		    .op() == Equality.EQUALS ? 75 : 60) : 110);
	    sp.printSubstTerm("{\\subst ", v, t.sub(0), 0, "}", t.sub(1),
		    assTarget);
	}
	
	private QuantifiableVariable instQV(Term t, LogicPrinter sp, int subTerm) {
	    QuantifiableVariable v = t.varsBoundHere(subTerm).get(0);

	    if (v instanceof SchemaVariable) {
		Object object = (sp.getInstantiations()
			.getInstantiation((SchemaVariable) v));
		if (object != null) {
		    Debug.assertTrue(object instanceof Term);
		    Debug
		    .assertTrue(((Term) object).op() instanceof QuantifiableVariable);
		    v = (QuantifiableVariable) (((Term) object).op());
		}
	    }
	    return v;
	}
    }

    
    /**
     * The standard concrete syntax for function and predicate terms.
     */
    public static final class FunctionNotation extends Notation {

	public FunctionNotation() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printFunctionTerm(t);
	}
    }

    
    /**
     * The standard concrete syntax for casts.
     */
    public static final class CastFunction extends Notation {

	final String pre, post;

	final int ass;

	public CastFunction(String pre, String post, int prio, int ass) {
	    super(prio);
	    this.pre = pre;
	    this.post = post;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printCast(pre, post, t, ass);
	}
    }
    

    /**
     * The standard concrete syntax for observer function terms.
     */
    static class ObserverNotation extends Notation {

        public ObserverNotation() {
            super(130);
        }

        protected ObserverNotation(int assoc) {
            super(assoc);
        }

        @Override
        public void print(Term t, LogicPrinter sp) throws IOException {
            sp.printObserver(t, null);
        }

        public void printWithHeap(Term t, LogicPrinter sp, Term heapTerm) throws IOException {
            sp.printObserver(t, heapTerm);
        }
    }

    /**
     * The standard concrete syntax for select.
     */
    public static final class SelectNotation extends ObserverNotation {
        public SelectNotation() {
            super(140);
        }

        @Override
        public void print(Term t, LogicPrinter sp) throws IOException {
            sp.printSelect(t, null);
        }

        @Override
        public void printWithHeap(Term t, LogicPrinter sp, Term heapTerm) throws IOException {
            sp.printSelect(t, heapTerm);
        }
    }

    /**
     * The standard concrete syntax for heap constructors.
     */
    public static class HeapConstructorNotation extends Notation {
        public HeapConstructorNotation() {
            super(140);
        }

        public void print(Term t, LogicPrinter sp) throws IOException {
            sp.printHeapConstructor(t, true);
        }

        public void printEmbeddedHeap(Term t, LogicPrinter sp) throws IOException {
            sp.printHeapConstructor(t, false);
        }
    }

    /**
     * The standard concrete syntax for store.
     */
    public static final class StoreNotation extends HeapConstructorNotation {

        public void print(Term t, LogicPrinter sp) throws IOException {
            sp.printStore(t, true);
        }

        public void printEmbeddedHeap(Term t, LogicPrinter sp) throws IOException {
            sp.printStore(t, false);
        }
    }


    /**
     * The standard concrete syntax for length.
     */
    public static final class Postfix extends Notation {
        
        private final String postfix;
        
	public Postfix(String postfix) {
	    super(130);
	    this.postfix = postfix;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printPostfix(t,postfix);
	}
    }       
    
    
    /**
     * The standard concrete syntax for singleton sets.
     */
    public static final class SingletonNotation extends Notation {

	public SingletonNotation() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printSingleton(t);
	}
    }
    
    /**
     * The standard concrete syntax for the element of operator.
     */
    public static final class ElementOfNotation extends Notation {
        private String symbol;

	public ElementOfNotation() {
	    super(130);
	}
	
	    public ElementOfNotation(String symbol){
	        this();
	        this.symbol = symbol;
	    }

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printElementOf(t, symbol);
	}
    }      
    
    
    
    /**
     * The standard concrete syntax for set comprehension.
     */
    
    
    /**
     * The standard concrete syntax for conditional terms
     * <code>if (phi) (t1) (t2)</code>.
     */
    public static final class IfThenElse extends Notation {

	private final String keyword;

	public IfThenElse(int priority, String keyw) {
	    super(priority);
	    keyword = keyw;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printIfThenElseTerm(t, keyword);
	}
    }

    
    /**
     * The standard concrete syntax for all kinds of variables.
     */
    public static class VariableNotation extends Notation {
	public VariableNotation() {
	    super(1000);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (t.op() instanceof ProgramVariable) {
		sp
			.printConstant(t.op().name().toString().replaceAll(
				"::", "."));
	    } else {
		Debug.out("Unknown variable type");
		sp.printConstant(t.op().name().toString());
	    }
	}
    }

    
    public static final class SchemaVariableNotation extends VariableNotation {

	@SuppressWarnings("unchecked")
    public void print(Term t, LogicPrinter sp) throws IOException {
	    // logger.debug("SSV: " + t+ " [" + t.op() + "]");
	    Debug.assertTrue(t.op() instanceof SchemaVariable);
	    Object o = sp.getInstantiations().getInstantiation(
		    (SchemaVariable) (t.op()));
	    if (o == null) {
		// logger.debug("Instantiation of " + t+ " [" + t.op() + "]" + "
                // not known.");
		sp.printConstant(t.op().name().toString());
	    } else {
		if (o instanceof ProgramElement) {
		    // logger.debug(t.toString() + " [" + t.op() + "]" + "
                        // is a ProgramElement.");
		    sp.printProgramElement((ProgramElement) o);
		} else {
		    // logger.debug("Instantiation of " + t+ " [" + t.op() +
                        // "]" + " known.");
		    if (o instanceof ImmutableList) {
            final Iterator<Object> it = ((ImmutableList<Object>) o)
				.iterator();
			sp.getLayouter().print("{");
			while (it.hasNext()) {
			    final Object next = it.next();
			    if (next instanceof Term) {
				sp.printTerm((Term) o);
			    } else {
				sp.printConstant(o.toString());
			    }
			    if (it.hasNext()) {
				sp.getLayouter().print(",");
			    }
			}
			sp.getLayouter().print("}");
		    } else {
			Debug.assertTrue(o instanceof Term);
			sp.printTerm((Term) o);
		    }
		}
	    }
	}
    }

    
    /**
     * The standard concrete syntax for the number literal indicator `Z'.
     * This is only used in the `Pretty&amp;Untrue' syntax.
     */
    static final class NumLiteral extends Notation {
	public NumLiteral() {
	    super(120);
	}

	public static String printNumberTerm(Term numberTerm) {
	    Term t = numberTerm;

	    // skip number symbol /as this method may be called
	    // e.g. by char literal we do not fail if the first is
	    // not the number symbol
	    if (t.op().name().equals(IntegerLDT.NUMBERS_NAME)) {
		t = t.sub(0);
	    }

	    final StringBuffer number = new StringBuffer();
	    int offset = 0;

	    if (t.op().name().toString().equals(
		    IntegerLDT.NEGATIVE_LITERAL_STRING)) {
		number.append("-");
		t = t.sub(0);
		offset = 1;
	    }

	    do {
		final String opName = t.op().name() + "";

		if (t.arity() != 1
			|| (opName.length() != 1 || !Character.isDigit(opName
				.charAt(0)))) {
		    return null; // not a number
		} else {
		    number.insert(offset, opName);
		}
		t = t.sub(0);
	    } while (t.arity() != 0);

	    return number.toString();
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    final String number = printNumberTerm(t);
	    if (number != null) {
		sp.printConstant(number);
	    } else {
		sp.printFunctionTerm(t);
	    }
	}
    }
    

    /**
     * The standard concrete syntax for the character literal indicator `C'.
     */
    static final class CharLiteral extends Notation {
	public CharLiteral() {
	    super(1000);
	}

	private static String printCharTerm(Term t) {

	    char charVal = 0;
	    int intVal = 0;

	    String result = NumLiteral.printNumberTerm(t.sub(0));

	    if (result == null) {
		return null;
	    }

	    try {
		intVal = Integer.parseInt(result);
		charVal = (char) intVal;
		if (intVal - charVal != 0)
		    throw new NumberFormatException(); // overflow!

	    } catch (NumberFormatException ex) {
		System.out.println("Oops. " + result + " is not of type char");
		return null;
	    }

	    return ("'" + Character.valueOf(charVal)) + "'";
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    final String charString = printCharTerm(t);
	    if (charString != null) {
		sp.printConstant(charString);
	    } else {
		sp.printFunctionTerm(t);
	    }
	}
    }
    

  

    /**
     * The standard concrete syntax for sequence singletons.
     */
    public static final class SeqSingletonNotation extends Notation {
        final String lDelimiter, rDelimiter;

	public SeqSingletonNotation(String lDelimiter, String rDelimiter) {
	    super(130);
            this.lDelimiter = lDelimiter;
            this.rDelimiter = rDelimiter;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printSeqSingleton(t, lDelimiter, rDelimiter);
	}
    }
    
    public static final class SeqConcatNotation extends Notation {

        private final Function seqSingleton;
        private final Function seqConcat;
        private final Function charLiteral;


        public SeqConcatNotation(Function seqConcat, Function seqSingleton, Function charLiteral) {           
            super(130);
            this.seqConcat = seqConcat;
            this.seqSingleton = seqSingleton;
            this.charLiteral = charLiteral;
        }

        
        private String printStringTerm(Term t) {
            String result = "\"";
            Term term = t;
            while (term.op().arity() == 2) {
              result = result
                + CharLiteral.printCharTerm(term.sub(0).sub(0)).charAt(1);
              term = term.sub(1);
            }
            result = result
                    + CharLiteral.printCharTerm(term.sub(0)).charAt(1);            
            return (result + "\"");
        }
        
        @Override
        public void print(Term t, LogicPrinter sp) throws IOException {
            if (isCharLiteralSequence(t)) {
                final String sLit;
                try {
                    sLit = printStringTerm(t);
                } catch (Exception e) {
                    sp.printFunctionTerm(t);                    
                    return;
                }                
                sp.printConstant(sLit);
            } else {
                sp.printFunctionTerm(t);
            }
        }


        private boolean isCharLiteralSequence(Term t) {            
            if (t.op() == seqConcat && isCharLiteralSequenceHelp(t.sub(0))) {
                return isCharLiteralSequenceHelp(t.sub(1)) || isCharLiteralSequence(t.sub(1));
            } 
            return false;
        }


        private boolean isCharLiteralSequenceHelp(Term t) {
            return (t.op() == seqSingleton && t.sub(0).op() == charLiteral);
        }

    }
    
    public static final class SeqGetNotation extends Notation {

        public SeqGetNotation() {
            /*
             * Not sure what value to choose here.
             * (Kai Wallisch 10/2014)
             */
            super(130);
        }

        @Override
        public void print(Term t, LogicPrinter sp) throws IOException {
            sp.printSeqGet(t);
        }

    }

}