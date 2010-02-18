// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.ppAndJavaASTExtension;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * This extended PrettyPrinter generates java code that can be written to a file
 * and be compiled. This is also possible with the ordinary PrettyPrinter when
 * its attribute fileWriterMode is set to true. (The file writing capability
 * could be completely extracted to this class). This class can additionally
 * handle SyntacticalProgramVariables and SyntacticalTypeRefs whose only purpose
 * is to be printable by the PrettyPrinter, but are not supposed to be used by
 * other parts of the system like JavaInfo.
 * 
 * @author gladisch
 */
public class CompilableJavaCardPP extends PrettyPrinter {

    /**
     * This field is set to true after the first error. This is to prevent
     * multiple notifications about similar errors.
     */
    private static boolean errorOccurred = false;

    public CompilableJavaCardPP(final Writer o, final boolean noLinefeed) {
	super(o, noLinefeed);
    }

    /**
     * This method is implemented analogously to {@code
     * de.uka.ilkd.key.java.PrettyPrinter.printProgramVariable}
     */
    public void printSyntacticalProgramVariable(
	    final SyntacticalProgramVariable x) throws java.io.IOException {

	printHeader(x);
	writeInternalIndentation(x);
	// Assuming fileWriterMode is true
	write(x.name().toString().substring(
	        x.name().toString().lastIndexOf(":") + 1));
	printFooter(x);
    }

    /**
     * This method is implemented analogously to {@code printTypeReference} but
     * it is independet from KeYJavaTypes which is the whole idea behind
     * SyntacticalTypeRef.
     */
    public void printSyntacticalTypeReference(final SyntacticalTypeRef x)
	    throws java.io.IOException {
	if (x.type instanceof ArrayDeclaration) {
	    printArrayDeclaration((ArrayDeclaration) x.type);
	} else if (x.getProgramElementName() != null) {
	    printHeader(x);
	    if (x.getReferencePrefix() != null) {
		writeElement(x.getReferencePrefix());
		writeToken(".", x);
	    }
	    writeElement(x.getProgramElementName());
	}
	printFooter(x);
    }

    /**
     * This method is copied from {@code
     * de.uka.ilkd.key.java.PrettyPrinter.writeElement}. The only difference is
     * that the ghost-modifier is not printed
     */
    @Override
    protected void writeElement(final int lf, final int levelChange,
	    int blanks, final SourceElement elem) throws IOException {
	if (!(elem instanceof Ghost)) {
	    level += levelChange;
	    if (lf > 0) {
		blanks += getTotalIndentation();
	    }
	    final SourceElement first = elem.getFirstElement();
	    Position indent = getRelativePosition(first);
	    if (indent == Position.UNDEFINED) {
		indent = new Position(lf, blanks);
	    } else {
		if (lf > indent.getLine()) {
		    indent = new Position(lf, indent.getColumn());
		}
		if (blanks > indent.getColumn()) {
		    indent = new Position(indent.getLine(), blanks);
		}
	    }
	    indentMap.put(first, indent);
	    elem.prettyPrint(this);
	}
    }

    /*
     * This is a bit dirty solution to handle the case that a SyntacticalXXX
     * class has beenused with the ordinary PrettyPrinter. E.g. if
     * SyntacticalTypeRef.prettyPrint iscalled with the normal PrettyPrinter.
     * This should not happen.
     * 
     * The approach is to use temporarily a new CompilableJavaPP and then to
     * print itscontent into the PrettyPrinter that is here expected as
     * argument.
     */
    public void emergencyPrint(final PrettyPrinter pp) throws IOException {
	final StringWriter sw = (StringWriter) out;
	final String s = sw.toString();
	if (!errorOccurred) {
	    errorOccurred = true;
	    // Shorten the output to fit into the dialogbox
	    final String sshort = s.length() > 80 ? s.substring(80) + "..." : s;

	    Main
		    .getInstance()
		    .notify(
		            new GeneralFailureEvent(
		                    "CodeError: Unexpected parametertype. The problem originates\n"
		                            + "from the syntax tree of the substring:\n "
		                            + sshort
		                            + "\n Despite this error an exception is not thrown and \n KeY will continue the current taks."));
	    Thread.dumpStack();
	}
	pp.write(s);
    }

    @Override
    public void printProgramVariable(final ProgramVariable x)
	    throws java.io.IOException {

	printHeader(x);
	writeInternalIndentation(x);
	write(x.name().toString().substring(
	        x.name().toString().lastIndexOf(":") + 1));

	printFooter(x);
    }

    @Override
    public void printStringLiteral(final StringLiteral x)
	    throws java.io.IOException {
	printHeader(x);
	writeInternalIndentation(x);
	if (!encodeUnicodeChars(x.getValue()).startsWith("\"")) {
	    write("\"");
	}
	write(encodeUnicodeChars(x.getValue()));
	if (!encodeUnicodeChars(x.getValue()).startsWith("\"")) {
	    write("\"");
	}
	printFooter(x);
    }

    @Override
    public void printClassDeclaration(final ClassDeclaration x)
	    throws java.io.IOException {
	classToPrint = x;
	printHeader(x);
	int m = 0;
	if (x.getModifiers() != null) {
	    m = x.getModifiers().size();
	}
	if (m > 0) {
	    ImmutableArray<Modifier> mods = x.getModifiers();
	    mods = replacePrivateByPublic(mods);
	    writeKeywordList(mods);
	    m = 1;
	}
	if (x.getProgramElementName() != null) {
	    writeToken(m, "class", x);
	    writeElement(1, x.getProgramElementName());
	}
	if (x.getExtendedTypes() != null) {
	    writeElement(1, x.getExtendedTypes());
	}
	if (x.getImplementedTypes() != null) {
	    writeElement(1, x.getImplementedTypes());
	}
	if (x.getProgramElementName() != null) {
	    write(" {");
	} else { // anonymous class
	    write("{");
	}
	if (x.getMembers() != null) {
	    // services.getJavaInfo().getKeYProgModelInfo().getConstructors(kjt)
	    if (!containsDefaultConstructor(x.getMembers())) {
		write("\n   public " + x.getProgramElementName() + "(){}\n");
	    }
	    writeBlockList(2, 1, 0, x.getMembers());
	}
	writeSymbol(1, (x.getMembers() != null) ? -1 : 0, "}");
	printFooter(x);
	classToPrint = null;
    }

    @Override
    public void printFieldDeclaration(final FieldDeclaration x)
	    throws java.io.IOException {
	if (!((ProgramVariable) x.getVariables().last().getProgramVariable())
	        .isImplicit()) {
	    printHeader(x);
	    int m = 0;
	    if (x.getModifiers() != null) {
		ImmutableArray<Modifier> mods = x.getModifiers();
		m = mods.size();
		if (x.isFinal()
		        && (!x.isStatic() || !(x.getVariables().get(0)
		                .getProgramVariable() instanceof ProgramConstant))) {
		    m--;
		    mods = removeFinal(mods);
		}
		writeKeywordList(mods);
	    }
	    writeElement((m > 0) ? 1 : 0, x.getTypeReference());
	    final ImmutableArray<? extends VariableSpecification> varSpecs = x
		    .getVariables();
	    assert varSpecs != null : "Strange: a field declaration without a"
		    + " variable specification";
	    writeCommaList(0, 0, 1, varSpecs);
	    write(";");
	    printFooter(x);

	    // provides a set method for each field. Necessary for unittest
	    // generation.

	    for (int i = 0; i < varSpecs.size(); i++) {
		final VariableSpecification varSpec = varSpecs.get(i);
		final ProgramVariable pv = (ProgramVariable) varSpec
		        .getProgramVariable();
		if (!(x.isFinal() && x.isStatic() && pv instanceof ProgramConstant)) {
		    final String pvName = pv.getProgramElementName()
			    .getProgramName();
		    String typeName;
		    final Type javaType = pv.getKeYJavaType().getJavaType();
		    if (javaType instanceof ArrayType) {
			typeName = ((ArrayType) javaType)
			        .getAlternativeNameRepresentation();
		    } else {
			typeName = javaType.getFullName();
		    }

		    final String typeNameNoBrackets = getTypeNameForAccessMethods(pv
			    .getKeYJavaType().getName());
		    printHeader(x);
		    write("\n\npublic " + (x.isStatic() ? "static " : "")
			    + "void _set" + pvName + typeNameNoBrackets + "("
			    + typeName + " _" + pvName + "){\n");
		    write("    " + pvName + " = _" + pvName + ";\n");
		    write("}");
		    write("\n\npublic " + (x.isStatic() ? "static " : "")
			    + typeName + " _" + pvName + typeNameNoBrackets
			    + "(){\n");
		    write("    return " + pvName + ";\n");
		    write("}");
		    printFooter(x);
		}
	    }

	}
    }

    @Override
    public void printMethodDeclaration(final MethodDeclaration x)
	    throws java.io.IOException {
	if (x.getFullName().indexOf("<") == -1) {
	    printHeader(x);
	    final Comment[] c = x.getComments();
	    int m = c.length;
	    for (final Comment element : c) {
		printComment(element);
	    }
	    if (x.getModifiers() != null) {
		ImmutableArray<Modifier> mods = x.getModifiers();
		if ((x instanceof ConstructorDeclaration)) {
		    mods = replacePrivateByPublic(mods);
		}
		m += mods.size();
		writeKeywordList(mods);
	    }
	    if (x.getTypeReference() != null) {
		if (m > 0) {
		    writeElement(1, x.getTypeReference());
		} else {
		    writeElement(x.getTypeReference());
		}
		writeElement(1, x.getProgramElementName());
	    } else if (x.getTypeReference() == null
		    && !(x instanceof ConstructorDeclaration)) {
		write(" void ");
		writeElement(1, x.getProgramElementName());
	    } else {
		if (m > 0) {
		    writeElement(1, x.getProgramElementName());
		} else {
		    writeElement(x.getProgramElementName());
		}
	    }
	    write(" (");
	    if (x.getParameters() != null) {
		writeCommaList(1, x.getParameters());
	    }
	    write(")");
	    if (x.getThrown() != null) {
		writeElement(1, x.getThrown());
	    }
	    if (x.getBody() != null) {
		writeElement(1, x.getBody());
	    } else {
		write(";");
	    }
	    printFooter(x);
	}
    }

    @Override
    public void printMethodBodyStatement(final MethodBodyStatement x)
	    throws java.io.IOException {

	final boolean wasNoLinefeed = noLinefeed;
	noLinefeed = false;

	printHeader(x);
	writeInternalIndentation(x);
	markStart(0, x);

	final IProgramVariable pvar = x.getResultVariable();
	if (pvar != null) {
	    writeElement(pvar);
	    write("=");
	}

	printMethodReference(x.getMethodReference(), false);
	write(";");
	markEnd(0, x);
	printFooter(x);

	noLinefeed = wasNoLinefeed;
    }

    @Override
    public void printComment(final Comment x) throws java.io.IOException {
	write("\n");
	if (x.getText().startsWith("/*")) {
	    write(x.getText());
	    if (x.getText().indexOf("*/") == -1) {
		write("*/");
	    }
	}
    }

    /**
     * A utility method to invoke e.toString where e is the argument. However,
     * if the argument has dynamic type JavaSourceElement, then use the
     * CompilableJavaPP and return the value of
     * e.toString(CompilableJavaPP,StringWriter). This is important to handle
     * the case that e contains a SyntacticalXXX object.
     */
    public static String toString(final de.uka.ilkd.key.java.Expression e) {
	if (e instanceof JavaSourceElement) {
	    final JavaSourceElement jse = (JavaSourceElement) e;
	    final StringWriter sw = new StringWriter();
	    final CompilableJavaPP cjpp = new CompilableJavaPP(sw, true);
	    return jse.toString(cjpp, sw);
	} else {
	    return e.toString();
	}
    }
}
