// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.io.*;
import java.util.HashMap;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.visitor.FieldReplaceVisitor;
import de.uka.ilkd.key.java.visitor.ReflFieldReplaceVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOp;
import de.uka.ilkd.key.logic.op.AttributeOp;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.unittest.AssGenFac.AssignmentGenerator;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.CompilableJavaCardPP;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.SyntacticalProgramVariable;
import de.uka.ilkd.key.util.ExtList;

/**
 * Generates a unittest for a given piece of code and a set of modelgenerators.
 */

public class TestGenFac {

    public final static String TG_JAVA = "Reflection API";

    public final static String TG_JAVACARD = "Setters & Getters";

    public static String testGenMode = TG_JAVA;

    public static int counter = 0;

    public TestGenerator create(final Services serv, final String fileName,
	    final String directory, final boolean testing,
	    final AssignmentGenerator ag, final TestGeneratorGUIInterface gui) {
	assert (testGenMode == TG_JAVACARD || testGenMode == TG_JAVA) : "Unhandled case in AssignmentGenerator.";
	if (testGenMode == TG_JAVACARD) {
	    return new JavaCardTestGenerator(serv, fileName, directory,
		    testing, ag, gui);
	} else {
	    return new JavaTestGenerator(serv, fileName, directory, testing, ag, gui);
	}
    }

    private class JavaCardTestGenerator extends TestGenerator {

	private JavaCardTestGenerator(final Services serv,
	        final String fileName, final String directory,
	        final boolean testing, final AssignmentGenerator ag,
	        final TestGeneratorGUIInterface gui) {
	    super(serv, fileName, directory, testing, ag, gui);
	}

	@Override
	protected void exportCodeUnderTest() {
	    for (final KeYJavaType kjt : ji.getAllKeYJavaTypes()) {
		final Type type = kjt.getJavaType();
		// mbender: we are only interested in ClassDeclaration or
		// InterfaceDeclaration
		if ((type instanceof ClassDeclaration)
		        || type instanceof InterfaceDeclaration) {
		    final String fn = ((TypeDeclaration) type)
			    .getPositionInfo().getFileName();
		    // Check if the current class is the one we want. Test is
		    // done by comparing the paths of the loaded Java classes
		    // and the path of the file to be tested
		    if (fn.indexOf(modDir) != -1) {
			final String fName = fn.substring(fn
			        .lastIndexOf(File.separator) + 1, fn.length());
			final String dName = fn.substring(fn
			        .indexOf(File.separator), fn
			        .lastIndexOf(File.separator) + 1);

			try {
			    final StringWriter sw = new StringWriter();
			    final CompilableJavaCardPP pp = new CompilableJavaCardPP(
				    sw, false);
			    // Write the implementation under test to the PP
			    // buffer
			    printDeclaration(pp, type);
			    writeToFile(dName, fName, sw);
			} catch (final IOException ioe) {
			    throw new UnitTestException(ioe);
			}
		    }
		}
	    }

	}

	@Override
	protected String getHeader(final String fName) {
	    String result = "";
	    final String lineSeparator = System.getProperty("line.separator");
	    BufferedReader reader;
	    try {
		reader = new BufferedReader(new FileReader(fName));
		String line;
		while ((line = reader.readLine()) != null) {
		    result += line + lineSeparator;
		}
		reader.close();
	    } catch (final IOException ioe) {
		throw new UnitTestException(ioe);
	    }
	    int declIndex = result.indexOf("class ");
	    if (declIndex == -1) {
		declIndex = result.indexOf("interface ");
	    }
	    result = result.substring(0, declIndex);
	    result = result.substring(0, result.lastIndexOf(";") + 1);
	    return result + "\n\n";
	}
    }

    private class JavaTestGenerator extends TestGenerator{

	private static final String DONT_COPY = "aux";

	private final String dontCopy;

	boolean callOracle;

	private final AccessMethodsManager amm;

	private JavaTestGenerator(final Services serv, final String fileName,
	        final String directory, final boolean testing,
	        final AssignmentGenerator ag,final TestGeneratorGUIInterface gui) {
	    super(serv, fileName, directory, testing, ag, gui);
	    dontCopy = modDir + File.separator + DONT_COPY;
	    callOracle = false;
	    amm = AccessMethodsManager.getInstance();
	}

	@Override
	protected MethodReference getOracle(Term post,
	        final SyntacticalProgramVariable buffer, final ExtList children) {
	    post = replaceConstants(post, serv, null);
	    callOracle = true;
	    final MethodReference res = (MethodReference) getMethodReferenceForFormula(
		    post, buffer, children);
	    callOracle = false;
	    return res;
	}

	@Override
	@SuppressWarnings("unchecked")
	protected Expression translateTerm(final Term t,
	        final SyntacticalProgramVariable buffer, final ExtList children) {
	    final Operator op = t.op();
	    if (!callOracle) {
		return super.translateTerm(t, buffer, children);
	    } else if (op instanceof AttributeOp) {
		final ExtList tchildren = new ExtList();
		tchildren.add(translateTerm(t.sub(0), buffer, children));
		final FieldReference fr = (FieldReference) ((AttributeOp) op)
		        .convertToProgram(t, tchildren);
		if ("length".equals(fr.getProgramVariable()
		        .getProgramElementName().getProgramName())) {
		    return amm.arrayLength(fr);
		} else {
		    return amm.callGetter(fr);
		}

	    } else if (op instanceof ArrayOp) {
		final ExtList tchildren = new ExtList();
		tchildren.add(translateTerm(t.sub(0), buffer, children));
		tchildren.add(translateTerm(t.sub(1), buffer, children));
		return amm.callGetter((ArrayReference) ((ArrayOp) op)
		        .convertToProgram(t, tchildren));
	    } else {
		return super.translateTerm(t, buffer, children);
	    }
	}

	@Override
	protected ProgramElement replace(final StatementBlock mBody) {
	    /*
	     * The visitor is applied on SyntacticalProgramVariable and the
	     * visitor must be implemented such that effectively
	     * CreatingASTVisitor.doDefaultAction(x) is invoked where x is the
	     * SyntacticalProgramVariable. For this the Visitor interface was be
	     * extended, to support actions on IProgramVariable from which
	     * SyntacticalProgramVariable is derived.
	     */
	    final FieldReplaceVisitor frv = new ReflFieldReplaceVisitor(mBody,
		    serv);
	    frv.start();
	    return frv.result();
	}

	@Override
	protected void exportCodeUnderTest() {
	    try {
		// Copy the involved classes without modification
		copy(modDir, directory + modDir);
	    } catch (final IOException e) {
		e.printStackTrace();
	    }

	    // Create WrapperClass
	    try {
		writeToFile(modDir + File.separator,
		        AccessMethodsManager.NAME_OF_CLASS + ".java", amm
		                .createClass());
	    } catch (final IOException ioe) {
		throw new UnitTestException(ioe);
	    } finally {
		amm.init();
	    }
	}

	@Override
	protected Expression createConstructorCall(final Sort sort,
	        final HashMap<String, NewArray> array2Cons,
	        final Expression loc1, final KeYJavaType locKJT) {
	    if (sort instanceof ArraySort) {
		    String arrayExpression = CompilableJavaCardPP.toString(loc1);
		    final Expression cons = array2Cons.get(arrayExpression);
		if (cons == null) {
			System.err.println("WARNING (TestGenFac.java):Problem with generating an array constructor for "+arrayExpression+
			"  An array of size 20 will be created but this is an emergency solution.");
		    return amm.callNew(new NewArray(
			    new Expression[] { new IntLiteral(20) },
			    new TypeRef(getBaseType(locKJT)), locKJT, null, 0));
		} else {
		    return cons;
		}
		/*
	         * KeYJavaType locKJT =loc1.getKeYJavaType(serv, null); ExtList
	         * aType = new ExtList(); aType.add(new TypeRef(locKJT)); cons =
	         * new NewArray(aType, locKJT, new ArrayInitializer(new
	         * ExtList()), 0);
	         */
	    } else {
		return amm.callNew(new New(new Expression[0], new TypeRef(
		        locKJT), null));
	    }
	}

	@Override
	protected String getHeader(final String fName) {
	    return "";
	}

	private void copy(final String srcName, final String targName)
	        throws IOException {
	    // We don't want to copy the Folder with API Reference
	    // Implementation
	    if (srcName.equals(dontCopy)) {
		return;
	    }
	    // Create the File with given filename and check if it exists and if
	    // it's readable
	    final File srcFile = new File(srcName);
	    if (!srcFile.exists()) {
		throw new IOException("FileCopy: " + "no such source file: "
		        + srcName);
	    }
	    if (!srcFile.canRead()) {
		throw new IOException("FileCopy: "
		        + "source file is unreadable: " + srcName);
	    }
	    if (srcFile.isDirectory()) {
		final String newTarget;
		if (srcName.equals(modDir)) {
		    newTarget = targName;
		} else {
		    newTarget = targName + File.separator + srcFile.getName();
		}
		for (final String subName : srcFile.list()) {
		    copy(srcName + File.separator + subName, newTarget);
		}
	    } else if (srcFile.isFile()) {
		final File targDir = new File(targName);
		if (!targDir.exists()) {
		    targDir.mkdirs();
		}
		final File targFile = new File(targDir, srcFile.getName());
		if (targFile.exists()) {
		    if (!targFile.canWrite()) {
			throw new IOException("FileCopy: "
			        + "destination file is unwriteable: "
			        + targName);
		    }
		}
		FileInputStream src = null;
		FileOutputStream targ = null;
		try {
		    src = new FileInputStream(srcFile);
		    targ = new FileOutputStream(targFile);
		    final byte[] buffer = new byte[4096];
		    int bytesRead;

		    while ((bytesRead = src.read(buffer)) != -1) {
			targ.write(buffer, 0, bytesRead); // write
		    }
		} finally {
		    if (src != null) {
			try {
			    src.close();
			} catch (final IOException e) {
            }
		    }
		    if (targ != null) {
			try {
			    targ.close();
			} catch (final IOException e) {
            }
		    }
		}
	    } else {
		throw new IOException("FileCopy: " + srcName
		        + " is neither a file nor a directory!");
	    }
	}

    }
}
