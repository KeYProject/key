// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest.ppAndJavaASTExtension;

import java.beans.Expression;
import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.java.JavaSourceElement;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.Ghost;

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
public class CompilableJavaPP extends PrettyPrinter {
    
    public CompilableJavaPP(Writer o, boolean noLinefeed) {
        super(o, noLinefeed, true);
    }

    /**
     * This method is implemented analogously to {@code
     * de.uka.ilkd.key.java.PrettyPrinter.printProgramVariable}
     */
    public void printSyntacticalProgramVariable(SyntacticalProgramVariable x)
            throws java.io.IOException {

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
    public void printSyntacticalTypeReference(SyntacticalTypeRef x)
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
    protected void writeElement(int lf, int levelChange, int blanks,
            SourceElement elem) throws IOException {
        if (!(elem instanceof Ghost)) {
            level += levelChange;
            if (lf > 0) {
                blanks += getTotalIndentation();
            }
            SourceElement first = elem.getFirstElement();
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

    /**This field is set to true after the first error. This is to prevent multiple notifications about similar errors. */
    protected static boolean errorOccurred=false;

    /*This is a bit dirty solution to handle the case that a SyntacticalXXX class has been
     *used with the ordinary PrettyPrinter. E.g. if SyntacticalTypeRef.prettyPrint is
     *called with the normal PrettyPrinter. This should not happen.
     *
     *The approach is to use temporarily a new CompilableJavaPP and then to print its
     *content into the PrettyPrinter that is here expected as argument.
     */
    public void emergencyPrint(PrettyPrinter pp)throws IOException{
	StringWriter sw = (StringWriter)out;
	String s=sw.toString();
	if(!errorOccurred){
	    errorOccurred=true;
	    String sshort = s.length()>80?s.substring(80)+"...":s; //Shorten the output to fit into the dialogbox
	    Main.getInstance().notify(new GeneralFailureEvent("CodeError: Unexpected parametertype. The problem originates\n" +
	    		"from the syntax tree of the substring:\n "+sshort+
	    		"\n Despite this error an exception is not thrown and \n KeY will continue the current taks."));
	    Thread.dumpStack();
	}
        pp.write(s);
    }
    
    /** A utility method to invoke e.toString where e is the argument. 
     * However, if the argument has dynamic type JavaSourceElement, 
     * then use the CompilableJavaPP and return the value of e.toString(CompilableJavaPP,StringWriter).
     * This is important to handle the case that e contains a SyntacticalXXX object.*/
    public static String toString(de.uka.ilkd.key.java.Expression e){
	if(e instanceof JavaSourceElement) {
	    JavaSourceElement jse = (JavaSourceElement)e;
	    StringWriter sw=new StringWriter();
	    CompilableJavaPP cjpp = new CompilableJavaPP(sw,true);
	    return jse.toString(cjpp, sw);
	}else{
	    return e.toString();
	}
    }
}
