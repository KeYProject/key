package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;

public class DLEmbeddedExpression extends Operator {

    private final Function functionSymbol;

    /**
     * @return the functionSymbol
     */
    public Function getFunctionSymbol() {
        return functionSymbol;
    }

    public DLEmbeddedExpression(Function f, ExtList children) {
        super(children);
        this.functionSymbol = f;
    }

    /**
     * Arity of an embedded JavaDL Expression depends upon the number of
     * arguments.
     */
    @Override
    public int getArity() {
        return functionSymbol.arity();
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.java.expression.Operator#getKeYJavaType(de.uka.ilkd.key.java.Services, de.uka.ilkd.key.java.reference.ExecutionContext)
     */
    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        
        Sort sort = functionSymbol.sort();
        
        KeYJavaType kjt = javaServ.getJavaInfo().getKeYJavaType(sort);
        if(kjt != null) {
            return kjt;
        } else {
            // FIXME FIXME FIXME Unknown types are maped to int.
            return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_INT);
        }
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public int getPrecedence() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnDLEmbeddedExpression(this);
    }
    
    @Override    
    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printDLEmbeddedExpression(this);
    }
}
