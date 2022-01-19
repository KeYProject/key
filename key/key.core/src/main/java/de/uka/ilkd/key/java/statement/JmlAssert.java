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

/**
 * A JML assert statement.
 *
 * @author Benjamin Takacs
 */
public class JmlAssert extends JavaStatement {

    //TODO: move the Kind enum somewhere else?
    //      or maybe just use a boolean?
    /**
     * the kind of the statement, assert or assume
     */
    private final TextualJMLAssertStatement.Kind kind;
    /**
     * the condition in parse tree form
     */
    private final LabeledParserRuleContext condition;
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
     * copy constructor allowing changes
     *
     * @param proto the element to copy
     * @param changeList the changes to be made
     */
    public JmlAssert(JmlAssert proto, ExtList changeList) {
        super(changeList, getOr(changeList, PositionInfo.class, proto.getPositionInfo()));
        this.kind = getOr(changeList, TextualJMLAssertStatement.Kind.class, proto.kind);
        this.condition = getOr(changeList, LabeledParserRuleContext.class, proto.condition);
        this.cond = getOr(changeList, Term.class, proto.cond);
    }

    //TODO: move into ExtList?
    private static <T> T getOr(ExtList changeList, Class<T> cl, T defaultValue) {
        T result = changeList.get(cl);
        return result == null ? defaultValue : result;
    }

    public TextualJMLAssertStatement.Kind getKind() {
        return kind;
    }

    /**
     * @return the condition in String form
     */
    public String getConditionText() {
        //TODO: this will lose whitespace, so e.g. \forall will not be printed correctly
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
