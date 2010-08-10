// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.rule.metaconstruct;

import java.util.HashMap;
import java.util.Iterator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
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
        Function mul = (Function) services.getNamespaces().functions().lookup(new Name("mul"));
        UpdateFactory uf = new UpdateFactory(services, services.getProof().simplifier());
        TermBuilder tb = TermBuilder.DF;
        Update atPreUpd = uf.skip();
        Iterator<Term> it = scope2ws.keySet().iterator();
        while(it.hasNext()){
            Term scope = it.next();
            Term left = tb.dot(scope, (ProgramVariable) ConsumedAtPre.cons.attribute());
            Term right = tb.func(add, tb.func(ConsumedAtPre.consAtPre, scope), 
                    tb.func(mul, term.sub(1), tb.func(ConsumedAtPre.wsAtPre, scope)));
            atPreUpd = uf.parallel(atPreUpd, uf.elementaryUpdate(left,right));
        }
        return uf.apply(atPreUpd, term.sub(2));
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

}
