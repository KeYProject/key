package de.uka.ilkd.key.unittest.ppAndJavaASTExtension;

import java.io.Writer;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;

/** 
 * This extended PrettyPrinter generates java code that can be written
 * to a file and be compiled. This is also possible with the ordinary
 * PrettyPrinter when its attribute fileWriterMode is set to true.
 * (The file writing capability could be completely extracted to this class).
 * This class can additionally handle SyntacticalProgramVariables and
 * SyntacticalTypeRefs whose only purpose is to be printable by
 * the PrettyPrinter, but are not supposed to be used by other
 * parts of the system like JavaInfo.
 * @author gladisch
 */
public class CompilableJavaPP extends PrettyPrinter {

    public CompilableJavaPP(Writer o, boolean noLinefeed) {
        super(o, noLinefeed, true);
    }
    

    /**
     * This method is implemented analogously to 
     * {@code de.uka.ilkd.key.java.PrettyPrinter.printProgramVariable} 
     */
   public void printSyntacticalProgramVariable(SyntacticalProgramVariable x)
            throws java.io.IOException {

        printHeader(x);
        writeInternalIndentation(x);
        //Assuming fileWriterMode is true
        write(x.name().toString().substring(
                    x.name().toString().lastIndexOf(":") + 1));
        printFooter(x);
    }
    
   /**
    * This method is implemented analogously to 
    * {@code printTypeReference} but it is independet from KeYJavaTypes
    * which is the whole idea behind SyntacticalTypeRef.
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
}
