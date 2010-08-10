// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class UpdateScope extends AbstractMetaOperator {

    public UpdateScope() {
        super(new Name("#updateScope"), 3);
    }
    
    @Override
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        LogicVariable lv = new LogicVariable(new Name("obj"), services.getJavaInfo().getJavaLangObjectAsSort());
        TermBuilder tb = TermBuilder.DF;
        Term lvTerm = tb.var(lv);
        Term left = tb.dot(lvTerm, services.getJavaInfo().
                getAttribute(ImplicitFieldAdder.IMPLICIT_MEMORY_AREA, 
                services.getJavaInfo().getJavaLangObject()));
        Term guard = tb.equals(left, term.sub(0));
        UpdateFactory uf = new UpdateFactory(services, services.getProof().simplifier());
        Update u = uf.elementaryUpdate(left, term.sub(1));
        u = uf.guard(guard, u);
        u = uf.quantify(lv, u);
        return uf.apply(u, term.sub(2));
//        return TermFactory.DEFAULT.createQuanUpdateTerm(
//                new ArrayOfQuantifiableVariable[]{new ArrayOfQuantifiableVariable(lv)}, 
//                new Term[]{guard}, 
//                new Term[]{left}, 
//                new Term[]{term.sub(1)},
//                term.sub(2));
    }
    
    public Sort sort(Term[] term) {
        return term[2].sort();
    }

}
