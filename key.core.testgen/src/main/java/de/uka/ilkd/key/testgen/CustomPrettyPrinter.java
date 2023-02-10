package de.uka.ilkd.key.testgen;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramVariable;

public class CustomPrettyPrinter extends PrettyPrinter {
    public CustomPrettyPrinter(StringBuilder o, boolean noLinefeed) {
        super(o, noLinefeed);
    }

    public void printMethodBodyStatement(MethodBodyStatement x) {

        boolean wasNoLinefeed = noLinefeed;
        noLinefeed = false;

        printHeader(x);
        writeInternalIndentation(x);
        markStart(0, x);

        IProgramVariable pvar = x.getResultVariable();
        if (pvar != null) {
            writeElement(pvar);
            write("=");
        }

        printMethodReference(x.getMethodReference(), false);
        // // CHG:
        // write("@");
        // final TypeReference tr = x.getBodySourceAsTypeReference();
        // if (tr instanceof SchemaTypeReference) {
        // printSchemaTypeReference((SchemaTypeReference) tr);
        // } else if (tr instanceof SchemaVariable) {
        // printSchemaVariable((SchemaVariable) tr);
        // } else {
        // printTypeReference(tr);
        // }
        write(";");
        markEnd(0, x);
        printFooter(x);

        noLinefeed = wasNoLinefeed;
    }
}
