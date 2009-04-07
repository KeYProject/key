package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.AtPreFactory;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class ConsumedAtPre extends AbstractMetaOperator {

    private static final AtPreFactory APF = AtPreFactory.INSTANCE;
    
    public static SVInstantiations svInstRef = null;
    public static Function consAtPre = null;
    public static Function wsAtPre = null;
    public static Operator cons = null;
    
    public ConsumedAtPre() {
        super(new Name("#consumedAtPre"), 2);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        if(term.sub(0).arity()<2) return term.sub(1);
        checkAtPre(svInst, term.sub(0), services);
        Update u = APF.createAtPreDefinition(cons, consAtPre, services);
        UpdateFactory uf = new UpdateFactory(services, services.getProof().simplifier());
        return uf.apply(u, term.sub(1));
    }
    
    public static void checkAtPre(SVInstantiations svInst, Term paramWS, Services services){
        if(svInstRef!=svInst){
            svInstRef = svInst;
            Term t = paramWS.sub(0);
            if(t.arity()>1){
                t = t.sub(0);
            }
            cons = t.op();
            consAtPre = APF.createAtPreFunction(cons, services);
            wsAtPre = APF.createAtPreFunction(cons, services);
        }
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

}
