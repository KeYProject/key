package de.uka.ilkd.key.java.recoderext;

import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import recoder.java.ProgramElement;
import recoder.java.SourceVisitor;
import recoder.java.Statement;
import recoder.java.statement.JavaStatement;

public class JmlAssert extends JavaStatement implements ProgramElement {

    private final TextualJMLAssertStatement.Kind kind;

    /* condition should be an Expression,
       but as KeY doesn't support some jml Expressions as Expression Objects
       e.g. \forall
       keep this as the parse tree for now
       (blockcontracts seem to handle this similar)
       TODO: do the visitors work good enought?
             compare with what is done for loop/block contracts
     */
    private final LabeledParserRuleContext condition;

    public JmlAssert(TextualJMLAssertStatement.Kind kind, LabeledParserRuleContext condition) {
        this.kind = kind;
        this.condition = condition;
    }

    public JmlAssert(JmlAssert proto) {
        super(proto);
        this.kind = proto.kind;
        this.condition = proto.condition;
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
    public ProgramElement getChildAt(int i) {
        throw new IndexOutOfBoundsException("JmlAssert has no program children");
    }

    @Override
    public int getChildPositionCode(ProgramElement programElement) {
        return 0;
    }

    @Override
    public boolean replaceChild(ProgramElement programElement, ProgramElement programElement1) {
        return false;
    }

    @Override
    public void accept(SourceVisitor sourceVisitor) {
        //TODO: is it fine to leave this blank?
    }

    @Override
    public Statement deepClone() {
        //TODO: clone condition?
        return new JmlAssert(this);
    }
}
