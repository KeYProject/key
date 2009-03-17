// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;

import java.io.IOException;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.ldt.AbstractIntegerLDT;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.IteratorOfObject;
import de.uka.ilkd.key.rule.ListOfObject;
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
    protected int priority;

    /** Create a Notation with a given priority. */
    protected Notation(int priority) {
	this.priority = priority;
    }

    /** get the priority of the term */
    public int getPriority() {
	return priority;
    }

    /**
         * Print a term to a {@link LogicPrinter}. Concrete subclasses override
         * this to call one of the <code>printXYZTerm</code> of
         * {@link LogicPrinter}, which do the layout.
         */
    public void print(Term t, LogicPrinter sp) throws IOException {
	if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
	    sp.printTerm(t);
	} else {
	    sp.printConstant(t.toString());
	    System.err.println("There is no registered Notation "
		    + "for the operator\n" + t.op());
	}
    }

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
    public static class Constant extends Notation {
	String name;

	public Constant(String name, int prio) {
	    super(prio);
	    this.name = name;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printConstant(name);
	}
    }

    /**
         * The standard concrete syntax for prefix operators.
         */
    public static class Prefix extends Notation {
	String name;

	int ass;

	public Prefix(String name, int prio, int ass) {
	    super(prio);
	    this.name = name;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printPrefixTerm(name, t.sub(0), ass);
	    }
	}

    }

    /**
         * The standard concrete syntax for infix operators.
         */
    public static class Infix extends Notation {
	String name;

	int assLeft, assRight;

	public Infix(String name, int prio, int assLeft, int assRight) {
	    super(prio);
	    this.name = name;
	    this.assLeft = assLeft;
	    this.assRight = assRight;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printInfixTerm(t.sub(0), assLeft, name, t.sub(1), assRight);
	    }
	}

	/**
         * Print a term without beginning a new block. This calls the
         * {@link LogicPrinter#printTermContinuingBlock(Term)} method.
         */
	public void printContinuingBlock(Term t, LogicPrinter sp)
		throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printInfixTermContinuingBlock(t.sub(0), assLeft, name, t
			.sub(1), assRight);
	    }
	}

    }

    /**
         * The standard concrete syntax for arrays.
         */
    public static class ArrayNot extends Notation {

	final private String[] arraySeparators;

	private final int[] ass;

	public ArrayNot(String[] arraySeparators, int prio, int[] ass) {
	    super(prio);
	    this.arraySeparators = arraySeparators;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printArray(arraySeparators, t, ass);
	    }
	}
    }

    /**
         * The standard concrete syntax for quantifiers.
         */
    public static class Quantifier extends Notation {
	String name;

	int ass;

	public Quantifier(String name, int prio, int ass) {
	    super(prio);
	    this.name = name;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printQuantifierTerm(name, t.varsBoundHere(0), t.sub(0), ass);
	    }
	}

    }

    /**
         * The standard concrete syntax for DL modalities box and diamond.
         */
    public static class Modality extends Notation {
	String left, right;

	int ass;

	public Modality(String left, String right, int prio, int ass) {
	    super(prio);
	    this.left = left;
	    this.right = right;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printModalityTerm(left, t.javaBlock(), right, t, ass);
	    }
	}
    }

    /**
         * The concrete syntax for DL modalities represented with a
         * SchemaVariable.
         */
    public static class ModalSVNotation extends Notation {
	int ass;

	public ModalSVNotation(int prio, int ass) {
	    super(prio);
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printModalityTerm("\\modality{" + t.op().name().toString()
			+ "}", t.javaBlock(), "\\endmodality", t, ass);
	    }
	}
    }

    /**
         * The standard concrete syntax for terms with updates.
         */
    public static class AnonymousUpdate extends Notation {

	public AnonymousUpdate() {
	    super(115);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		final int assTarget = (t.sort() == Sort.FORMULA ? (((IUpdateOperator) t
			.op()).target(t).op() == Op.EQUALS ? 75 : 60)
			: 110);
		sp.printAnonymousUpdate(t, assTarget);
	    }
	}
    }

    /**
         * The standard concrete syntax for terms with updates.
         */
    public static class QuanUpdate extends Notation {

	public QuanUpdate() {
	    super(115);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		final Operator targetOp = ((IUpdateOperator) t.op()).target(t)
			.op();
		final int assTarget = (t.sort() == Sort.FORMULA ? (targetOp
			.arity() == 1 ? 60 : 85) : 110);
		if (t.op() instanceof AnonymousUpdate) {
		    sp.printAnonymousUpdate(t, assTarget);
		} else {
		    sp.printQuanUpdateTerm("{", ":=", "}", t, 80, 0, assTarget);
		}
	    }
	}
    }

    /**
         * The standard concrete syntax for substitution terms.
         */
    public static class Subst extends Notation {
	public Subst() {
	    super(120);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		QuantifiableVariable v = instQV(t, sp, 1);
		final int assTarget = (t.sort() == Sort.FORMULA ? (t.sub(1)
			.op() == Op.EQUALS ? 75 : 60) : 110);
		sp.printSubstTerm("{\\subst ", v, t.sub(0), 0, "}", t.sub(1),
			assTarget);
	    }
	}
    }

    /**
         * The standard concrete syntax for function and predicate terms.
         */
    public static class Function extends Notation {

	public Function() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printFunctionTerm(t.op().name().toString(), t);
	    }
	}
    }

    /**
         * The standard concrete syntax for a non rigid function with explicit
         * known dependencies.
         */
    public static class NRFunctionWithDependenciesNotation extends Notation {

	public NRFunctionWithDependenciesNotation() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		final NRFunctionWithExplicitDependencies func = (NRFunctionWithExplicitDependencies) t
			.op();
		StringBuffer name = new StringBuffer(func.classifier());
		name
			.append(NRFunctionWithExplicitDependencies.DEPENDENCY_LIST_STARTER);

		final int depSize = func.dependencies().size();
		for (int i = 0; i < depSize; i++) {

		    Location loc = func.dependencies().getLocation(i);
		    if (loc instanceof ProgramVariable
			    && ((ProgramVariable) loc).isMember()) {
			loc = AttributeOp.getAttributeOp((ProgramVariable) loc);
		    }

		    if (loc instanceof AttributeOp) {
			name.append(Attribute.printName((AttributeOp) loc,
				null, null).substring(1));
		    } else {
			name.append(loc.name());
		    }
		    name
			    .append(NRFunctionWithExplicitDependencies.DEPENDENCY_LIST_SEPARATOR);
		}
		if (depSize == 0) {
		    name
			    .append(NRFunctionWithExplicitDependencies.DEPENDENCY_LIST_SEPARATOR);
		}
		name
			.append(NRFunctionWithExplicitDependencies.DEPENDENCY_LIST_END);
		sp.printFunctionTerm(name.toString(), t);
	    }
	}
    }

    /**
         * The standard concrete syntax for arrays.
         */
    public static class CastFunction extends Notation {

	final String pre, post;

	final int ass;

	public CastFunction(String pre, String post, int prio, int ass) {
	    super(prio);
	    this.pre = pre;
	    this.post = post;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printCast(pre, post, t, ass);
	    }
	}
    }

    /**
         * The standard concrete syntax for query terms <code>o.q(x)</code>.
         */
    static class ProgramMethod extends Notation {
	private final int ass;

	public ProgramMethod(int ass) {
	    super(130);
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else if (((de.uka.ilkd.key.logic.op.ProgramMethod) t.op())
		    .isStatic()) {

		sp.printFunctionTerm(t.op().name().toString().replaceAll("::",
			"."), t);
	    } else {
		final ProgramElementName name = (ProgramElementName) t.op()
			.name();
		sp.printQueryTerm(name.getProgramName() + "@("
			+ name.getQualifier() + ")", t, ass);
	    }
	}
    }
    
    //implemented by mbender for jmltest
    public static class JMLProgramMethod extends Notation {
        private final int ass;

        public JMLProgramMethod(int ass) {
            super(130);
            this.ass = ass;
        }

        public void print(Term t, LogicPrinter sp) throws IOException {
            if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
                sp.printTerm(t);
            } else if (((de.uka.ilkd.key.logic.op.ProgramMethod) t.op())
                    .isStatic()) {

                sp.printFunctionTerm(t.op().name().toString().replaceAll("::",
                        "."), t);
            } else {
                final ProgramElementName name = (ProgramElementName) t.op()
                        .name();
                sp.printQueryTerm(name.getProgramName(), t, ass);
            }
        }
    }

    /**
         * The standard concrete syntax for attribute terms <code>o.a</code>.
         */
    public static class Attribute extends Notation {

	private int associativity;

	public Attribute(int priority, int associativity) {
	    super(priority);
	    this.associativity = associativity;
	}

	/**
         * prints an attribute operator
         */
	public static String printName(AttributeOp op, Term refPrefix,
		LogicPrinter sp) {
	    final IProgramVariable ivar = op.attribute();
	    if (!(ivar instanceof ProgramVariable)) {
		return op.toString();
	    }
	    final ProgramVariable pvar = ((ProgramVariable) ivar);

	    final String qualifier = pvar.getProgramElementName()
		    .getQualifier();
	    final String programName = pvar.getProgramElementName()
		    .getProgramName();

	    if (qualifier.length() == 0
		    || (refPrefix != null && sp != null && sp.printInShortForm(
			    programName, refPrefix))) {
		return "." + programName;
	    }

	    return "." + programName + "@(" + qualifier + ")";

	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		if (t.op() instanceof AttributeOp) {
		    sp.printPostfixTerm(t.sub(0), associativity, printName(
			    (AttributeOp) t.op(), t.sub(0), sp));
		} else {
		    sp.printPostfixTerm(t.sub(0), associativity, "."
			    + t.op().name());
		}
	    }
	}
    }

    /**
         * The standard concrete syntax for attribute terms <code>o.a</code>.
         */
    public static class ShadowAttribute extends Notation {

	private int associativity;

	public ShadowAttribute(int priority, int associativity) {
	    super(priority);
	    this.associativity = associativity;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printShadowedAttribute(t.sub(0), associativity, Attribute
			.printName(((AttributeOp) t.op()), t.sub(0), sp), t
			.sub(1));
	    }
	}
    }

    /**
         * The standard concrete syntax for conditional terms
         * <code>if (phi) (t1) (t2)</code>.
         */
    public static class IfThenElse extends Notation {

	private final String keyword;

	public IfThenElse(int priority, String keyw) {
	    super(priority);
	    keyword = keyw;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
		sp.printTerm(t);
	    } else {
		sp.printIfThenElseTerm(t, keyword);
	    }
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

    public static class SortedSchemaVariableNotation extends VariableNotation {
	static Logger logger = Logger.getLogger(Notation.class.getName());

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
		    if (o instanceof ListOfObject) {
			final IteratorOfObject it = ((ListOfObject) o)
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

    public static class MetavariableNotation extends Notation {
	public MetavariableNotation() {
	    super(1000);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp
		    .printMetavariable((de.uka.ilkd.key.logic.op.Metavariable) t
			    .op());
	}
    }

    /**
         * The standard concrete syntax for the number literal indicator `Z'.
         * This is only used in the `Pretty&amp;Untrue' syntax.
         */
    static class NumLiteral extends Notation {
	public NumLiteral() {
	    super(120);
	}

	public static String printNumberTerm(Term numberTerm) {
	    Term t = numberTerm;

	    // skip number symbol /as this method may be called
	    // e.g. by char literal we do not fail if the first is
	    // not the number symbol
	    if (t.op().name().equals(AbstractIntegerLDT.NUMBERS_NAME)) {
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
		sp.printFunctionTerm(t.op().name().toString(), t);
	    }
	}
    }

    /**
         * The standard concrete syntax for the character literal indicator `C'.
         */
    static class CharLiteral extends Notation {
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

	    return ("'" + new Character(charVal)).toString() + "'";
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    final String charString = printCharTerm(t);
	    if (charString != null) {
		sp.printConstant(charString);
	    } else {
		sp.printFunctionTerm(t.op().name().toString(), t);
	    }
	}
    }

    /**
         * The standard concrete syntax for the string literal indicator `cat'
         * or `epsilon'.
         */
    static class StringLiteral extends Notation {

	public StringLiteral() {
	    super(1000);
	}

	public static String printStringTerm(Term t) {
	    String result = "\"";
	    Term term = t;
	    while (term.op().arity() != 0) {
		result = result
			+ CharLiteral.printCharTerm(term.sub(0)).charAt(1);
		term = term.sub(1);
	    }
	    return (result + "\"");
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printConstant(printStringTerm(t));
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for the OCL
         * "iterate" operation.
         */
    public static class OCLIterate extends Notation {

	public OCLIterate() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    QuantifiableVariable iterVar = t.varsBoundHere(2)
		    .getQuantifiableVariable(0);
	    QuantifiableVariable accVar = t.varsBoundHere(2)
		    .getQuantifiableVariable(1);
	    sp.printOCLIterateTerm(t.sub(0), "->", "iterate", "(", ""
		    + iterVar.name() + ":" + iterVar.sort().name(), "; ", ""
		    + accVar.name() + ":" + accVar.sort().name(), "=",
		    t.sub(1), " | ", t.sub(2), ")");
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for the OCL
         * collection operations with one iteration variable.
         */
    public static class OCLCollOpBoundVar extends Notation {
	String name;

	public OCLCollOpBoundVar(String name) {
	    super(130);
	    this.name = name;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    QuantifiableVariable iterVar = t.varsBoundHere(1)
		    .getQuantifiableVariable(0);
	    sp.printOCLCollOpBoundVarTerm(t.sub(0), "->", name, "(", ""
		    + iterVar.name() + ":" + iterVar.sort().name(), " | ", t
		    .sub(1), ")");
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for the OCL
         * collection operations without iteration variables.
         */
    public static class OCLCollOp extends Notation {
	String name;

	public OCLCollOp(String name) {
	    super(130);
	    this.name = name;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printOCLCollOpTerm(name, t);
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for the OCL
         * "dot" operations.
         */
    public static class OCLDotOp extends Notation {
	String name;

	int ass;

	public OCLDotOp(String name, int ass) {
	    super(130);
	    this.name = name;
	    this.ass = ass;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printQueryTerm(name, t, ass);
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for the OCL
         * if-then-else-endif operation.
         */
    public static class OCLIf extends Notation {

	public OCLIf() {
	    super(125);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printOCLIfTerm("if ", t.sub(0), "then ", t.sub(1), "else ", t
		    .sub(2), "endif");
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for OCL
         * collections.
         */
    public static class OCLCollection extends Notation {
	String name;

	public OCLCollection(String name) {
	    super(130);
	    this.name = name;
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.layouter.beginI(0);
	    sp.layouter.print(name + "{");
	    sp.printOCLCollectionTerm(t);
	    sp.layouter.print("}").end();
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for the OCL
         * wrapper predicate.
         */
    public static class OCLWrapper extends Notation {

	public OCLWrapper() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printOCLWrapperTerm(t);
	}
    }

    /**
         * Used for OCL Simplification. The standard concrete syntax for an OCL
         * invariant.
         */
    public static class OCLInvariant extends Notation {

	public OCLInvariant() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.printOCLInvariantTerm(t.sub(0), t.sub(1));
	}
    }

    /**
         * Used for OCL Simplification. The concrete syntax for a list of OCL
         * invariants.
         */
    public static class OCLListOfInvariants extends Notation {

	public OCLListOfInvariants() {
	    super(130);
	}

	public void print(Term t, LogicPrinter sp) throws IOException {
	    sp.layouter.beginI(0);
	    sp.layouter.brk(0, -1).print("[\n");
	    sp.printOCLListOfInvariantsTerm(t);
	    sp.layouter.print("\n]").end();
	}
    }

    /**
         * @param t
         * @param sp
         * @param subTerm
         *                TODO
         * @return the quantified variable
         */
    protected QuantifiableVariable instQV(Term t, LogicPrinter sp, int subTerm) {
	QuantifiableVariable v = t.varsBoundHere(subTerm)
		.getQuantifiableVariable(0);

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
