package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.sort.Sort;

public abstract class MetaScopeAnnotation extends AbstractMetaOperator {

    public MetaScopeAnnotation(Name name, int arity){
        super(name, arity);
    }
    
    protected MethodBodyStatement getMethodBodyStatement(Term t){
        ProgramElement p = t.javaBlock().program();
        while(!(p instanceof MethodBodyStatement)){
            if(p instanceof StatementBlock){
                p = ((StatementBlock) p).getStatementAt(0);
            }else{
                p = (ProgramElement) p.getFirstElement();
            }
        }
        return (MethodBodyStatement) p;
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

}
