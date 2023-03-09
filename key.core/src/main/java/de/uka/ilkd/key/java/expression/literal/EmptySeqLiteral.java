package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;



public class EmptySeqLiteral extends Literal {

    public static final EmptySeqLiteral INSTANCE = new EmptySeqLiteral();

    private EmptySeqLiteral() {}


    @Override
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        return o == this;
    }


    public void visit(Visitor v) {
        v.performActionOnEmptySeqLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    }

    @Override
    public Name getLDTName() {
        return SeqLDT.NAME;
    }
}
