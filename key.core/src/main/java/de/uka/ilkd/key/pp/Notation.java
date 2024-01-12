/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.ldt.DoubleLDT;
import de.uka.ilkd.key.ldt.FloatLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Debug;

import org.key_project.util.collection.ImmutableList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Encapsulate the concrete syntax used to print a term. The {@link NotationInfo} class associates a
 * Notation with every {@link de.uka.ilkd.key.logic.op.Operator}. The various inner classes of this
 * class represent different kinds of concrete syntax, like prefix, infix, postfix, function style,
 * attribute style, etc.
 */
public abstract class Notation {
    private static final Logger LOGGER = LoggerFactory.getLogger(Notation.class);

    /**
     * The priority of this operator in the given concrete syntax. This is used to determine whether
     * parentheses are required around a subterm.
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
     * Print a term to a {@link LogicPrinter}. Concrete subclasses override this to call one of the
     * <code>printXYZTerm</code> of {@link LogicPrinter}, which do the layout.
     */
    public abstract void print(Term t, LogicPrinter sp);

    /**
     * Print a term without beginning a new block. See
     * {@link LogicPrinter#printTermContinuingBlock(Term)}for the idea behind this. The standard
     * implementation just delegates to {@link #print(Term,LogicPrinter)}
     */
    public void printContinuingBlock(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
            sp.printInfixTerm(t.sub(0), assLeft, name, t, t.sub(1), assRight);
        }

        /**
         * Print a term without beginning a new block. This calls the
         * {@link LogicPrinter#printTermContinuingBlock(Term)} method.
         */
        public void printContinuingBlock(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
            assert t.op() instanceof Modality;
            assert t.javaBlock() != null;
            sp.printModalityTerm(left, t.javaBlock(), right, t, ass);
        }
    }


    /**
     * The concrete syntax for DL modalities represented with a SchemaVariable.
     */
    public static final class ModalSVNotation extends Notation {
        private final int ass;

        public ModalSVNotation(int prio, int ass) {
            super(prio);
            this.ass = ass;
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printModalityTerm("\\modality{" + t.op().name().toString() + "}", t.javaBlock(),
                "\\endmodality", t, ass);
        }
    }


    /**
     * The standard concrete syntax for update application.
     */
    public static final class UpdateApplicationNotation extends Notation {

        public UpdateApplicationNotation() {
            super(115);
        }

        public void print(Term t, LogicPrinter sp) {
            assert t.op() == UpdateApplication.UPDATE_APPLICATION;
            final Operator targetOp = UpdateApplication.getTarget(t).op();
            final int assTarget =
                (t.sort() == Sort.FORMULA ? (targetOp.arity() == 1 ? 60 : 85) : 110);

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

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
            QuantifiableVariable v = instQV(t, sp, 1);
            final int assTarget =
                (t.sort() == Sort.FORMULA ? (t.sub(1).op() == Equality.EQUALS ? 75 : 60) : 110);
            sp.printSubstTerm("{\\subst ", v, t.sub(0), 0, "}", t.sub(1), assTarget);
        }

        private QuantifiableVariable instQV(Term t, LogicPrinter sp, int subTerm) {
            QuantifiableVariable v = t.varsBoundHere(subTerm).get(0);

            if (v instanceof SchemaVariable) {
                Object object = (sp.getInstantiations().getInstantiation((SchemaVariable) v));
                if (object != null) {
                    Debug.assertTrue(object instanceof Term);
                    Debug.assertTrue(((Term) object).op() instanceof QuantifiableVariable);
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

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
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
        public void print(Term t, LogicPrinter sp) {
            sp.printObserver(t, null);
        }

        public void printWithHeap(Term t, LogicPrinter sp, Term heapTerm) {
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
        public void print(Term t, LogicPrinter sp) {
            sp.printSelect(t, null);
        }

        @Override
        public void printWithHeap(Term t, LogicPrinter sp, Term heapTerm) {
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

        public void print(Term t, LogicPrinter sp) {
            sp.printHeapConstructor(t, true);
        }

        public void printEmbeddedHeap(Term t, LogicPrinter sp) {
            sp.printHeapConstructor(t, false);
        }
    }

    /**
     * The standard concrete syntax for store.
     */
    public static final class StoreNotation extends HeapConstructorNotation {

        public void print(Term t, LogicPrinter sp) {
            sp.printStore(t, true);
        }

        public void printEmbeddedHeap(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
            sp.printPostfix(t, postfix);
        }
    }


    /**
     * The standard concrete syntax for singleton sets.
     */
    public static final class SingletonNotation extends Notation {

        public SingletonNotation() {
            super(130);
        }

        public void print(Term t, LogicPrinter sp) {
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

        public ElementOfNotation(String symbol) {
            this();
            this.symbol = symbol;
        }

        public void print(Term t, LogicPrinter sp) {
            sp.printElementOf(t, symbol);
        }
    }

    /**
     * The standard concrete syntax for conditional terms <code>if (phi) (t1) (t2)</code>.
     */
    public static final class IfThenElse extends Notation {

        private final String keyword;

        public IfThenElse(int priority, String keyw) {
            super(priority);
            keyword = keyw;
        }

        public void print(Term t, LogicPrinter sp) {
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

        public void print(Term t, LogicPrinter sp) {
            if (t.op() instanceof ProgramVariable) {
                sp.printConstant(t.op().name().toString().replaceAll("::", "."));
            } else if (t.op() instanceof LogicVariable) {
                sp.printConstant(t.op().name().toString());
            } else {
                LOGGER.debug("Unknown variable type for VariableNotation: " + t.op());
                sp.printConstant(t.op().name().toString());
            }
        }
    }


    public static final class SchemaVariableNotation extends VariableNotation {

        @SuppressWarnings("unchecked")
        public void print(Term t, LogicPrinter sp) {
            // logger.debug("SSV: " + t+ " [" + t.op() + "]");
            Debug.assertTrue(t.op() instanceof SchemaVariable);
            Object o = sp.getInstantiations().getInstantiation((SchemaVariable) (t.op()));
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
                        final Iterator<Object> it = ((ImmutableList<Object>) o).iterator();
                        sp.layouter().print("{");
                        while (it.hasNext()) {
                            final Object next = it.next();
                            if (next instanceof Term) {
                                sp.printTerm((Term) o);
                            } else {
                                sp.printConstant(o.toString());
                            }
                            if (it.hasNext()) {
                                sp.layouter.print(",");
                            }
                        }
                        sp.layouter().print("}");
                    } else {
                        Debug.assertTrue(o instanceof Term);
                        sp.printTerm((Term) o);
                    }
                }
            }
        }
    }


    /**
     * The standard concrete syntax for the number literal indicator `Z'. This is only used in the
     * `Pretty&amp;Untrue' syntax.
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

            final StringBuilder number = new StringBuilder();
            int offset = 0;

            if (t.op().name().toString().equals(IntegerLDT.NEGATIVE_LITERAL_STRING)) {
                number.append("-");
                t = t.sub(0);
                offset = 1;
            }

            do {
                final String opName = String.valueOf(t.op().name());

                if (t.arity() != 1
                        || (opName.length() != 1 || !Character.isDigit(opName.charAt(0)))) {
                    return null; // not a number
                } else {
                    number.insert(offset, opName);
                }
                t = t.sub(0);
            } while (t.arity() != 0);

            return number.toString();
        }

        public void print(Term t, LogicPrinter sp) {
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
        private static final Logger LOGGER = LoggerFactory.getLogger(CharLiteral.class);

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
                if (intVal - charVal != 0) {
                    throw new NumberFormatException(); // overflow!
                }

            } catch (NumberFormatException ex) {
                LOGGER.error("Oops. {} is not of type char", result);
                return null;
            }

            return ("'" + charVal) + "'";
        }

        public void print(Term t, LogicPrinter sp) {
            final String charString = printCharTerm(t);
            if (charString != null) {
                sp.printConstant(charString);
            } else {
                sp.printFunctionTerm(t);
            }
        }
    }

    /**
     * The standard concrete syntax for the float literal indicator `FP'.
     */
    static final class FloatLiteral extends Notation {

        private final static int EXP_MASK = 0x7f80_0000;

        public FloatLiteral() {
            super(120);
        }

        public static String printFloatTerm(Term floatTerm) {

            if (!floatTerm.op().name().equals(FloatLDT.FLOATLIT_NAME)) {
                return null;
            }

            try {
                int bits = extractValue(floatTerm.sub(0));
                float f = Float.intBitsToFloat(bits);
                if (Float.isNaN(f)) {
                    return "floatNaN";
                } else if (f == Float.POSITIVE_INFINITY) {
                    return "floatInf";
                } else if (f == Float.NEGATIVE_INFINITY) {
                    return "-floatInf";
                } else {
                    return f + "f";
                }
            } catch (NumberFormatException e) {
                return null;
            }
        }

        private static int extractValue(Term t) {
            if (t.op().name().toString().equals("#")) {
                return 0;
            } else {
                int digit = Integer.parseInt(t.op().name().toString());
                return digit + 10 * extractValue(t.sub(0));
            }
        }

        public void print(Term t, LogicPrinter sp) {
            final String number = printFloatTerm(t);
            if (number != null) {
                sp.printConstant(number);
            } else {
                sp.printFunctionTerm(t);
            }
        }
    }

    /**
     * The standard concrete syntax for the double literal indicator `DFP'.
     */
    static final class DoubleLiteral extends Notation {
        public DoubleLiteral() {
            super(120);
        }

        public static String printDoubleTerm(Term doubleTerm) {

            if (!doubleTerm.op().name().equals(DoubleLDT.DOUBLELIT_NAME)) {
                return null;
            }

            try {
                long bits = extractValue(doubleTerm.sub(0));
                double f = Double.longBitsToDouble(bits);
                if (Double.isNaN(f)) {
                    return "floatNaN";
                } else if (f == Double.POSITIVE_INFINITY) {
                    return "doubleInf";
                } else if (f == Double.NEGATIVE_INFINITY) {
                    return "-doubleInf";
                } else {
                    return f + "d";
                }
            } catch (NumberFormatException e) {
                return null;
            }
        }

        private static long extractValue(Term t) {
            if (t.op().name().toString().equals("#")) {
                return 0L;
            } else {
                int digit = Integer.parseInt(t.op().name().toString());
                return digit + 10 * extractValue(t.sub(0));
            }
        }

        public void print(Term t, LogicPrinter sp) {
            final String number = printDoubleTerm(t);
            if (number != null) {
                sp.printConstant(number);
            } else {
                sp.printFunctionTerm(t);
            }
        }
    }


    /**
     * The standard concrete syntax for sequence singletons.
     */
    public static final class SeqSingletonNotation extends Notation {
        final String lDelimiter;
        final String rDelimiter;

        public SeqSingletonNotation(String lDelimiter, String rDelimiter) {
            super(130);
            this.lDelimiter = lDelimiter;
            this.rDelimiter = rDelimiter;
        }

        public void print(Term t, LogicPrinter sp) {
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
            StringBuilder result = new StringBuilder("\"");
            Term term = t;
            while (term.op().arity() == 2) {
                result.append(CharLiteral.printCharTerm(term.sub(0).sub(0)).charAt(1));
                term = term.sub(1);
            }
            result.append(CharLiteral.printCharTerm(term.sub(0)).charAt(1));
            return (result + "\"");
        }

        @Override
        public void print(Term t, LogicPrinter sp) {
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
             * Not sure what value to choose here. (Kai Wallisch 10/2014)
             */
            super(130);
        }

        @Override
        public void print(Term t, LogicPrinter sp) {
            sp.printSeqGet(t);
        }

    }

}
