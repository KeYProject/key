package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
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
    private final TextualJMLAssertStatement.Kind kind;
    private final LabeledParserRuleContext condition;
    private Term cond;

    public JmlAssert(TextualJMLAssertStatement.Kind kind, LabeledParserRuleContext condition) {
        this.kind = kind != null ? kind : TextualJMLAssertStatement.Kind.ASSERT;
        this.condition = condition;
    }

    public JmlAssert(TextualJMLAssertStatement.Kind kind, LabeledParserRuleContext condition, PositionInfo positionInfo) {
        super(positionInfo);
        this.kind = kind;
        this.condition = condition;
    }

    public JmlAssert(TextualJMLAssertStatement.Kind kind, LabeledParserRuleContext condition, ExtList changeList) {
        super(changeList);
        this.kind = getOr(changeList, TextualJMLAssertStatement.Kind.class, kind);
        this.condition = getOr(changeList, LabeledParserRuleContext.class, condition);
    }

    public JmlAssert(JmlAssert proto, LabeledParserRuleContext condition) {
        super(proto.getPositionInfo());
        kind = proto.kind;
        this.condition = condition;
        this.cond = proto.cond;
    }

    public JmlAssert(JmlAssert x, ExtList changeList) {
        super(changeList, x.getPositionInfo());
        this.kind = getOr(changeList, TextualJMLAssertStatement.Kind.class, x.kind);
        this.condition = getOr(changeList, LabeledParserRuleContext.class, x.condition);
        this.cond = getOr(changeList, Term.class, x.cond);
    }

    //TODO: move into ExtList?
    private static <T> T getOr(ExtList changeList, Class<T> cl, T defaultValue) {
        T result = changeList.get(cl);
        return result == null ? defaultValue : result;
    }

    public TextualJMLAssertStatement.Kind getKind() {
        return kind;
    }

    public LabeledParserRuleContext getCondition() {
        return condition;
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
        final var specType = kind == TextualJMLAssertStatement.Kind.ASSERT
                ? OriginTermLabel.SpecType.ASSERT
                : OriginTermLabel.SpecType.ASSUME;
        this.cond = jmlIo.translateTerm(condition, specType);
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
