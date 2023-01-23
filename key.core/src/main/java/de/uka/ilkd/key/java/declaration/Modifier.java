package de.uka.ilkd.key.java.declaration;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.TerminalProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;

/**
 * Modifier. taken from COMPOST and changed to achieve an immutable structure
 */

public abstract class Modifier extends JavaProgramElement implements TerminalProgramElement {

    /**
     * Modifier.
     */

    public Modifier() {}

    /**
     * Modifier.
     *
     * @param children May contain: some Comments
     */
    public Modifier(ExtList children) {
        super(children);
    }

    /**
     * Get symbol.
     *
     * @return the string.
     */

    protected abstract String getSymbol();

    /**
     * Get symbol text.
     *
     * @return the symbol text.
     */
    public String getText() {
        return getSymbol();
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnModifier(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printModifier(this);
    }
}
