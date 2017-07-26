package de.uka.ilkd.key.java.expression.literal;

import java.math.BigInteger;
import org.key_project.util.ExtList;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;

/**
 * This class is a superclass for integer literals (Bigint, Int, Long, Char).
 * It provides a getValue() method to receive the actual value of the literal as well as
 * getValueString() to get a String representation.
 * @author Wolfram Pfeifer
 */
public abstract class AbstractIntegerLiteral extends Literal {

    /**
     * This field indicates if the literal is directly (may be separated by whitespace or comments,
     * but not parentheses) surrounded by an unary minus.
     * This information is needed to be able to perform correct range checks for bounded literals.
     */
    protected final boolean surroundedByUnaryMinus;

    /**
     * Sets surroundedUnaryMinus to false.
     */
    protected AbstractIntegerLiteral() {
        surroundedByUnaryMinus = false;
    }

    /**
     * Constructor to set the surroundedByUnaryMinus flag.
     * @param surroundedByUnaryMinus flag used for range checks
     */
    protected AbstractIntegerLiteral(boolean surroundedByUnaryMinus) {
        this.surroundedByUnaryMinus = surroundedByUnaryMinus;
    }

    /**
     * Constructor for Recoder2KeY transformation.
     *
     * @param children the children of this AST element as KeY classes, may contain: Comments
     * @param surroundedByUnaryMinus flag used for range checks
     */
    protected AbstractIntegerLiteral(ExtList children, boolean surroundedByUnaryMinus) {
        super(children);
        this.surroundedByUnaryMinus = surroundedByUnaryMinus;
    }

    /**
     *
     * @return true if the literal is directly surrounded by an unary minus and false if not
     */
    public boolean isSurroundedByUnaryMinus() {
        return surroundedByUnaryMinus;
    }

    /**
     *
     * @return the actual value of the literal as a BigInteger
     */
    public abstract BigInteger getValue();

    /**
     *
     * @return the actual value of the literal converted to a decimal String. If the literal
     *         represents a negative value, the first character is a '-' sign.
     */
    public abstract String getValueString();

    // TODO: equals
    @Override
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        if (!(o.getClass() == this.getClass())) {
            return false;
        }
        return ((AbstractIntegerLiteral)o).getValue().equals(getValue());
    }

    @Override
    public String toString() {
        return getValueString();
    }

    @Override
    public int hashCode() {
        int result = 17;
        result = 37 * result + getValue().hashCode();
        return result;
    }

    @Override
    public Name getLDTName() {
        return IntegerLDT.NAME;
    }
}
