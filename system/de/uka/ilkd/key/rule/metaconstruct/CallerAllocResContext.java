package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class CallerAllocResContext extends AbstractMetaOperator {

    public CallerAllocResContext(){
        super(new Name("#callerAllocResContext"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        MethodFrame mf = getInnermostMethodFrame(term.sub(0), services);
        boolean car=false;
        if(mf.getProgramMethod()!=null && mf.getProgramMethod().getMethodDeclaration()!=null){
            car = mf.getProgramMethod().getMethodDeclaration().callerAllocatedResult();
        }
        return termFactory.createJunctorTerm(car ? Op.TRUE : Op.FALSE);
    }
    
    public MethodFrame getInnermostMethodFrame(Term term, Services services) {
        //ignore updates
        while(term.op() instanceof IUpdateOperator) {
            term = term.sub(((IUpdateOperator)term.op()).targetPos());
        }
        
        //the remaining term should have a Java block 
        final ProgramElement pe = term.javaBlock().program();
                
        //fetch "self" from innermost method-frame
        MethodFrame result = new JavaASTVisitor(pe, services) {
            private MethodFrame result;
            private boolean done = false;
            protected void doDefaultAction(SourceElement node) {
                if(node instanceof MethodFrame && !done) {
                    done = true;
                    result = (MethodFrame) node;
                }
            }
            public MethodFrame run() {
                walk(pe);
                return result;
            }
        }.run();
                
        return result;
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

}
