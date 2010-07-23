package de.uka.ilkd.key.rtsj.rule.metaconstruct;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class WSAtPre extends AbstractMetaOperator {

    public WSAtPre() {
        super(new Name("#wsAtPre"), 2);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        HashMap<Term,Term> scope2ws = extractScope2WSMapping(term.sub(0));
        ConsumedAtPre.checkAtPre(svInst, term.sub(0), services);
        UpdateFactory uf = new UpdateFactory(services, services.getProof().simplifier());
        TermBuilder tb = TermBuilder.DF;
        Update atPreUpd = uf.skip();
        Iterator<Term> it = scope2ws.keySet().iterator();
        while(it.hasNext()){
            Term scope = it.next();
            Term left = tb.func(ConsumedAtPre.wsAtPre, scope);
            atPreUpd = uf.parallel(atPreUpd, uf.elementaryUpdate(left,scope2ws.get(scope)));
        }
        return uf.apply(atPreUpd, term.sub(1));
    }
    
    public static HashMap<Term,Term> extractScope2WSMapping(Term t){
        HashMap<Term,Term> scope2ws = new HashMap<Term,Term>();
        if(t.arity()<2) return scope2ws;
        Term scope;
        Term ws;
        while(t.op() == Op.AND){
            scope = t.sub(0).sub(0).sub(0);
            ws = t.sub(0).sub(1);
            scope2ws.put(scope, ws);
        }
        scope = t.sub(0).sub(0);
        ws = t.sub(1);
        scope2ws.put(scope, ws);
        return scope2ws;
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

}
