package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class StackForConstructedScope extends AbstractMetaOperator {

    public StackForConstructedScope() {
        super(new Name("#stackForConstructedScope"), 4);
    }

    /** calculates the resulting term. 
     */
    public Term calculate(Term term, SVInstantiations svInst, 
                          Services services) {  
    
        MethodReference mr = getMethodReference(term.sub(0));
        Term mem=term.sub(1);
        if(mr.callerScope()){
            mem=term.sub(3);
        }else if(mr.reentrantScope()){
            mem = termFactory.createAttributeTerm
            (services.getJavaInfo().getAllAttributes
             ("memoryArea", services.getJavaInfo().getJavaLangObject()).head(),
             term.sub(2));
        }else if(mr.constructedScope()){
            mem=term.sub(3);
        }
        KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(term.sub(1).sort());
        return termFactory.createAttributeTerm(
                services.getJavaInfo().getAllAttributes("stack", kjt).head(), mem);
    }
    
    private MethodReference getMethodReference(Term t){
        ProgramElement p = t.javaBlock().program();
        while(!(p instanceof MethodBodyStatement)){
            if(p instanceof StatementBlock){
                p = ((StatementBlock) p).getStatementAt(0);
            }else{
                p = (ProgramElement) p.getFirstElement();
            }
        }
        return ((MethodBodyStatement) p).getMethodReference();
    }

    public boolean mayBeAliasedBy(Location loc) {
        return true;
    }

    public Sort sort() {        
        return METASORT;
    }
    
}
