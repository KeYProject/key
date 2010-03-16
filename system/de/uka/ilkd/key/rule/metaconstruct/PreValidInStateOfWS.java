package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.FormulaWithAxioms;

public class PreValidInStateOfWS extends AbstractMetaOperator {

    public PreValidInStateOfWS() {
        super(new Name("#preValidInStateOfWS"), 2);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        if(!(term.sub(1).op() instanceof WorkingSpaceRigidOp)){
            return TermBuilder.DF.ff();
        }
        Term t0 = removeUpdates(term.sub(0));
        if(!((IWorkingSpaceOp) t0.op()).getProgramMethod().equals(
                ((IWorkingSpaceOp) term.sub(1).op()).getProgramMethod())){
            return TermBuilder.DF.ff();
        }
        WorkingSpaceNonRigidOp wso = (WorkingSpaceNonRigidOp) t0.op();
        return applySeqUpdateToPreRec(term.sub(0),
                ((WorkingSpaceRigidOp) term.sub(1).op()).getPre(wso.getSelf(t0), 
                        wso.getParameters(t0), services), 
                new UpdateFactory(services, new UpdateSimplifier()), services);
    }
    
    private Term removeUpdates(Term t){
        while(t.op() instanceof IUpdateOperator){
            t = ((IUpdateOperator) t.op()).target(t);
        }
        return t;
    }
    
    public static Term applySeqUpdateToPreRec(Term t0, Term t1, UpdateFactory uf, Services services){
        if(!(t0.op() instanceof IUpdateOperator)){
            return t1;
        }
        final Update u = Update.createUpdate ( t0 );
        final IUpdateOperator updateOp = (IUpdateOperator) t0.op();
        final Term target = updateOp.target ( t0 );
        return uf.apply ( u, applySeqUpdateToPreRec(target, t1, uf, services));
    }
    
/*    public static FormulaWithAxioms applySeqUpdateToPreRec(Term t0, 
            FormulaWithAxioms form, UpdateFactory uf, Services services){
        return new FormulaWithAxioms(applySeqUpdateToPreRec(t0, form.getFormula(), uf, services),
                applySeqUpdateToPreRec(t0, form.getAxiomsAsFormula(), uf, services));
    }*/
        
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
