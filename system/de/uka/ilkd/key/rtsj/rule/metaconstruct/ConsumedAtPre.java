// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.rule.metaconstruct;

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
    public static AttributeOp cons = null;
    
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
            cons = (AttributeOp) t.op();
            consAtPre = APF.createAtPreFunction(cons, services);
            services.getNamespaces().functions().add(consAtPre);
            wsAtPre = APF.createAtPreFunction(cons, services);
            services.getNamespaces().functions().add(wsAtPre);
        }
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }

}
