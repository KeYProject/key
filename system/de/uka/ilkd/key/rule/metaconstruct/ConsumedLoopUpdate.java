package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class ConsumedLoopUpdate extends AbstractMetaOperator {

    public ConsumedLoopUpdate() {
        super(new Name("#consumedLoopUpdate"), 3);
    }

    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        HashMap<Term,Term> scope2ws = WSAtPre.extractScope2WSMapping(term.sub(0));
        ConsumedAtPre.checkAtPre(svInst, term.sub(0), services);
        Function add = (Function) services.getNamespaces().functions().lookup(new Name("add"));
        Function mult = (Function) services.getNamespaces().functions().lookup(new Name("mult"));
        UpdateFactory uf = new UpdateFactory(services, services.getProof().simplifier());
        TermBuilder tb = TermBuilder.DF;
        Update atPreUpd = uf.skip();
        Iterator<Term> it = scope2ws.keySet().iterator();
        while(it.hasNext()){
            Term scope = it.next();
            Term left = tb.func((Function) ConsumedAtPre.cons, scope);
            Term right = tb.func(add, tb.func(ConsumedAtPre.consAtPre, scope), 
                    tb.func(mult, term.sub(1), tb.func(ConsumedAtPre.wsAtPre, scope)));
            atPreUpd = uf.parallel(atPreUpd, uf.elementaryUpdate(left,right));
        }
        return uf.apply(atPreUpd, term.sub(2));
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

}
