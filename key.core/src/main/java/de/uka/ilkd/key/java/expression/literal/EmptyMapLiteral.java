package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.MapLDT;
import de.uka.ilkd.key.logic.Name;

public class EmptyMapLiteral extends Literal {

    public static final EmptyMapLiteral INSTANCE = new EmptyMapLiteral();

    private EmptyMapLiteral() {
    }

    @Override
    public boolean equalsModRenaming(SourceElement o, NameAbstractionTable nat) {
        return o == this;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnEmptyMapLiteral(this);
    }

    @Override
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptyMapLiteral(this);
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_MAP);
    }

    @Override
    public Name getLDTName() {
        return MapLDT.NAME;
    }

}
