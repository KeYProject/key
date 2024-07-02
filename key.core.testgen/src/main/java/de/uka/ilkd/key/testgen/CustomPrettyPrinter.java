package de.uka.ilkd.key.testgen;

import java.io.Writer;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class CustomPrettyPrinter extends PrettyPrinter {
	public CustomPrettyPrinter(Writer o) {
		super(o);

	}

	public CustomPrettyPrinter(Writer o, SVInstantiations svi) {
		super(o, svi);

	}

	public CustomPrettyPrinter(Writer o, boolean noLinefeed) {
		super(o, noLinefeed);

	}

	public CustomPrettyPrinter(Writer o, boolean noLinefeed,
			SVInstantiations svi) {
		super(o, noLinefeed, svi);

	}

	public void printMethodBodyStatement(MethodBodyStatement x)
			throws java.io.IOException {

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
//		// CHG:
//		write("@");
//		final TypeReference tr = x.getBodySourceAsTypeReference();
//		if (tr instanceof SchemaTypeReference) {
//			printSchemaTypeReference((SchemaTypeReference) tr);
//		} else if (tr instanceof SchemaVariable) {
//			printSchemaVariable((SchemaVariable) tr);
//		} else {
//			printTypeReference(tr);
//		}
		write(";");
		markEnd(0, x);
		printFooter(x);

		noLinefeed = wasNoLinefeed;
	}
}
