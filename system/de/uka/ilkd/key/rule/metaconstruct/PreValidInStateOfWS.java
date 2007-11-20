package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class PreValidInStateOfWS extends AbstractMetaOperator {

    public PreValidInStateOfWS() {
        super(new Name("#preValidInStateOfWS"), 2);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        if(!(term.sub(1).op() instanceof WorkingSpaceRigidOp)){
            return TermBuilder.DF.ff();
        }
        Term t0 = term.sub(0);
        while(t0.op() instanceof IUpdateOperator){
            t0 = ((IUpdateOperator) t0.op()).target(t0);
        }
        if(!((IWorkingSpaceOp) t0.op()).getProgramMethod().equals(
                ((IWorkingSpaceOp) term.sub(1).op()).getProgramMethod())){
            return TermBuilder.DF.ff();
        }
        if(!(term.sub(0).op() instanceof IUpdateOperator)){
            return ((WorkingSpaceRigidOp) term.sub(1).op()).getPre();
        }
        return applySeqUpdateToPreRec(term.sub(0),
                ((WorkingSpaceRigidOp) term.sub(1).op()).getPre(), 
                new UpdateFactory(services, new UpdateSimplifier()));
    }
    
    public static Term applySeqUpdateToPreRec(Term t0, Term t1, UpdateFactory uf){
        if(!(t0.op() instanceof IUpdateOperator)){
            return ((WorkingSpaceNonRigidOp) t0.op()).getProgramVariableReplacer().replace(t1);
        }
        final Update u = Update.createUpdate ( t0 );
        final IUpdateOperator updateOp = (IUpdateOperator) t0.op();
        final Term target = updateOp.target ( t0 );
        return uf.apply ( u, applySeqUpdateToPreRec(target, t1, uf));
    }
    
    public Sort sort(){
        return Sort.FORMULA;
    }
    
    /** Unlike other meta operators this one returns a formula
     * not a term.
     */
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
    
}
