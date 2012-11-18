package de.uka.ilkd.key.java.expression.literal;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;

public class FreeLiteral extends Literal {
    
    public final static FreeLiteral INSTANCE = new FreeLiteral();

    @Override
    public void visit(Visitor v) {
        // TODO Auto-generated method stub

    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ) {
        return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_FREE_ADT);
    }

}
