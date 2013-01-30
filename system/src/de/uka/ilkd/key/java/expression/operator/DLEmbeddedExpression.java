package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.ConvertException;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
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
        
        KeYJavaType kjt = getKeYJavaType(javaServ, sort);
        if(kjt != null) {
            return kjt;
        } else {
            // FIXME FIXME FIXME Unknown types are mapped to int.
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

    public void check(Services javaServ) throws ConvertException {
        
        if(functionSymbol == null)
            throw new ConvertException("null function symbol");
        
        int expected = functionSymbol.arity();
        int actual = children.size();
        
        if (expected != actual) {
            throw new ConvertException("Function symbol " + functionSymbol
                    + " requires " + expected
                    + " arguments, but received only " + actual);
        }
        
        for (int i = 0; i < expected; i++) {
            Sort argSort = functionSymbol.argSort(i);
            KeYJavaType kjtExpected = getKeYJavaType(javaServ, argSort);
                
            Expression child = children.get(i);
            KeYJavaType kjtActual = javaServ.getTypeConverter().getKeYJavaType(child);
            
            // or use equals here?! Subtyping?!
            // if unknown type (null), be content and go on
            // XXX Check this
            if(kjtExpected != null && !kjtActual.getSort().extendsTrans(kjtExpected.getSort())) {
                throw new ConvertException("Received " + child
                        + " as argument " + i + " for function "
                        + functionSymbol + ". Was expecting type "
                        + kjtExpected + ", but received " + kjtActual);
            }
        }
    }

    private KeYJavaType getKeYJavaType(Services javaServ, Sort argSort) {
        // JavaInfo returns wrong data for sort integer! We need to find it over
        // other paths.
        JavaInfo javaInfo = javaServ.getJavaInfo();
        KeYJavaType intType = javaInfo.getPrimitiveKeYJavaType("int");
        if(argSort == intType.getSort()) {
            return intType;
        } else {
            return javaInfo.getKeYJavaType(argSort);
        }
    }
}
