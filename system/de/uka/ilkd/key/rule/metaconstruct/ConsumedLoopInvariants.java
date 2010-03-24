package de.uka.ilkd.key.rule.metaconstruct;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ConsumedLoopInvariants extends AbstractMetaOperator {

    public ConsumedLoopInvariants() {
        super(new Name("#consumedInv"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        HashMap<Term,Term> scope2ws = WSAtPre.extractScope2WSMapping(term.sub(0));
        ConsumedAtPre.checkAtPre(svInst, term.sub(0), services);
        Function sub = (Function) services.getNamespaces().functions().lookup(new Name("sub"));
        Function leq = (Function) services.getNamespaces().functions().lookup(new Name("leq"));
        TermBuilder tb = TermBuilder.DF;
        Term inv = tb.tt();
        Iterator<Term> it = scope2ws.keySet().iterator();
        while(it.hasNext()){
            Term scope = it.next();
            Term left = tb.func(sub, tb.dot(scope, (ProgramVariable) ConsumedAtPre.cons.attribute()), 
                    tb.func(ConsumedAtPre.consAtPre, scope));
            Term right = tb.func(ConsumedAtPre.wsAtPre, scope);
            inv = tb.and(inv, tb.func(leq, left, right));
        }
        return inv;
    }

    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

    
}
