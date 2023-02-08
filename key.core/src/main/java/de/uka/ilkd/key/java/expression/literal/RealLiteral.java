package de.uka.ilkd.key.java.expression.literal;

import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.RealLDT;
import de.uka.ilkd.key.logic.Name;

/**
 * JML \real literal.
 *
 * @author bruns
 */

public class RealLiteral extends Literal {

    /**
     * Textual representation of the value.
     */

    protected final String value;

    /**
     * Double literal.
     */

    public RealLiteral() {
        this.value = "0.0";
    }

    public RealLiteral(int value) {
        this("" + value + ".0");
    }

    public RealLiteral(double value) {
        this.value = "" + value;
    }

    public RealLiteral(java.math.BigDecimal value) {
        this.value = "" + value;
    }

    public RealLiteral(ExtList children, String value) {
        super(children);
        this.value = value;
    }

    public RealLiteral(ExtList children) {
        super(children);
        value = "0.0";
    }

    /**
     * Double literal.
     *
     * @param value a string.
     */

    public RealLiteral(String value) {
        this.value = value;
    }

    /**
     * tests if equals
     */
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o instanceof RealLiteral)) {
            return false;
        }
        return ((RealLiteral) o).getValue().equals(getValue());
    }

    @Override
    public int computeHashCode() {
        return 17 * super.computeHashCode() + getValue().hashCode();
    }

    /**
     * Get value.
     *
     * @return the string.
     */

    public String getValue() {
        return value;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        // v.performActionOnDoubleLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        // p.printDoubleLiteral(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_REAL);
    }

    @Override
    public Name getLDTName() {
        return RealLDT.NAME;
    }

}
