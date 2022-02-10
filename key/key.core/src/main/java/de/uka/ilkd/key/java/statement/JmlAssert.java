package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.key_project.util.ExtList;

import java.io.IOException;
import java.util.Objects;

/**
 * A JML assert statement.
 *
 * @author Benjamin Takacs
 */
public class JmlAssert extends JavaStatement {

    /**
     * the kind of the statement, assert or assume
     */
    private final TextualJMLAssertStatement.Kind kind;
    /**
     * the condition in parse tree form
     */
    private LabeledParserRuleContext condition;
    /**
     * the condition in Term form
     */
    private Term cond;

    /**
     *
     * @param kind assert or assume
     * @param condition the condition of this statement
     * @param positionInfo the position information for this statement
     */
    public JmlAssert(TextualJMLAssertStatement.Kind kind,
                     LabeledParserRuleContext condition,
                     PositionInfo positionInfo) {
        super(positionInfo);
        this.kind = kind;
        this.condition = condition;
    }

    /**
     *
     * @param children the children of this element
     */
    public JmlAssert(ExtList children) {
        super(children);
        this.kind = children.get(TextualJMLAssertStatement.Kind.class);
        this.condition = children.get(LabeledParserRuleContext.class);
        this.cond = children.get(Term.class);
        if ((cond == null) == (condition == null)) {
            throw new IllegalArgumentException("exactly one of cond and condition has to be null");
        }
    }

    public TextualJMLAssertStatement.Kind getKind() {
        return kind;
    }

    /**
     * @return the condition in String form
     */
    public String getConditionText() {
        if (cond != null) {
            return cond.toString();
        }
        // this will lose whitespace, so e.g. \forall will not be printed correctly
        // but normally the term form should get printed.
        return condition.first.getText().substring(kind.name().length());
    }

    /**
     * Returns the condition in Term form.
     *
     * You have to call translateCondition(JmlIO) before getting useful values.
     *
     * @return the condition in Term form if it was already translated else null
     */
    public Term getCond() {
        return cond;
    }


    /**
     * Translates the condition of this JML assert statement to a Term.
     *
     * Use as soon as possible, but can only be called once.
     *
     * @param jmlIo the JmlIO to use to translate the condition
     * @throws IllegalStateException if this JmlAssert already has a condition in Term form
     */
    public void translateCondition(final JmlIO jmlIo) {
        if (cond != null) {
            throw new IllegalStateException("condition can only be set once");
        }
        this.cond = jmlIo.translateTerm(condition);
        condition = null;
    }

    @Override
    public boolean equals(final Object o) {
        if (this == o) {
            return true;
        }
        if (!super.equals(o)) {
            return false;
        }
        //super.equals() check classes
        final JmlAssert jmlAssert = (JmlAssert) o;
        return kind == jmlAssert.kind &&
                Objects.equals(condition, jmlAssert.condition) &&
                Objects.equals(cond, jmlAssert.cond);
    }

    // hashCode() caches the result of computeHashCode()
    // so override that instead of hashCode which is final
    @Override
    protected int computeHashCode() {
        return Objects.hash(super.computeHashCode(), kind, condition, cond);
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public ProgramElement getChildAt(int index) {
        throw new IndexOutOfBoundsException("JmlAssert has no program children");
    }

    @Override
    public void prettyPrint(PrettyPrinter w) throws IOException {
        w.printJmlAssert(this);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnJmlAssert(this);
    }
}
