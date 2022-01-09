package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.key_project.util.ExtList;

import java.io.IOException;

public class JmlAssert extends JavaStatement implements ProgramElement {

    private final TextualJMLAssertStatement.Kind kind;
    private final LabeledParserRuleContext condition;

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
    }

    public JmlAssert(JmlAssert x, ExtList changeList) {
        super(changeList, x.getPositionInfo());
        this.kind = getOr(changeList, TextualJMLAssertStatement.Kind.class, x.kind);
        this.condition = getOr(changeList, LabeledParserRuleContext.class, x.condition);
    }

    //TODO: move into ExtList?
    private static <T> T getOr(ExtList changeList, Class<T> cl, T default_) {
        T result = changeList.get(cl);
        return result == null ? default_ : result;
    }

    public TextualJMLAssertStatement.Kind getKind() {
        return kind;
    }

    public LabeledParserRuleContext getCondition() {
        return condition;
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
