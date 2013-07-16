// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.AuxiliaryTermLabel;
import junit.framework.TestCase;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import static junit.framework.Assert.assertFalse;
import static junit.framework.Assert.assertTrue;

public class TestSelectsSimplifiedCondition extends TestCase {
    TermBuilder TB = TermBuilder.DF;
    Services services = TacletForTests.services();

    public void testTermsWithLeagalSelects() throws Exception {
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        Term baseHeap = TB.var(services.getTypeConverter().getHeapLDT().getHeap());
        Term nonAuxiliaryHeap = TB.func(new Function(new Name("heapFunc"), heapSort));
        Term auxiliaryHeap = TB.label(nonAuxiliaryHeap, AuxiliaryTermLabel.INSTANCE);
        Term o = TB.NULL(services);
        Term f = TB.func(services.getTypeConverter().getHeapLDT().getCreated());
        Term selectOfBaseHeap = TB.select(services, heapSort, baseHeap, o, f);
        Term selectOfAuxiliaryHeap = TB.select(services, heapSort, auxiliaryHeap, o, f);

        Term term = selectOfBaseHeap;
        assertTrue("selectOfBaseHeap failed", testCondition(term, false));
        assertFalse("negated selectOfBaseHeap failed", testCondition(term, true));

        term = selectOfAuxiliaryHeap;
        assertTrue("selectOfAuxiliaryHeap failed", testCondition(term, false));
        assertFalse("negated selectOfAuxiliaryHeap failed", testCondition(term, true));
    }

    public void testTermsWithIlleagalSelects() throws Exception {
        Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();
        Term baseHeap = TB.var(services.getTypeConverter().getHeapLDT().getHeap());
        Term nonAuxiliaryHeap = TB.func(new Function(new Name("heapFunc"), heapSort));
        Term auxiliaryHeap = TB.label(nonAuxiliaryHeap, AuxiliaryTermLabel.INSTANCE);
        Term o = TB.NULL(services);
        Term f = TB.func(services.getTypeConverter().getHeapLDT().getCreated());
        Term selectOfBaseHeap = TB.select(services, heapSort, TB.store(services, baseHeap, o, f, o), o, f);
        Term selectOfAuxiliaryHeap = TB.select(services, heapSort, TB.store(services, auxiliaryHeap, o, f, o), o, f);
        Term selectOfNonAuxiliaryHeap = TB.select(services, heapSort, nonAuxiliaryHeap, o, f);

        Term term = selectOfBaseHeap;
        assertFalse(testCondition(term, false));
        assertTrue(testCondition(term, true));

        term = selectOfAuxiliaryHeap;
        assertFalse(testCondition(term, false));
        assertTrue(testCondition(term, true));

        term = selectOfNonAuxiliaryHeap;
        assertFalse(testCondition(term, false));
        assertTrue(testCondition(term, true));
    }

    private boolean testCondition(Term term, boolean negation) {
        SchemaVariable var = SchemaVariableFactory.createTermSV(new Name("var"), Sort.ANY);
        SelectsSimplifiedCondition cond = new SelectsSimplifiedCondition(var, negation);

        SVInstantiations svInst = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        svInst = svInst.add(var, term, services);

        MatchConditions mc = MatchConditions.EMPTY_MATCHCONDITIONS.setInstantiations(svInst);
        mc = cond.check(var, term, mc, services);

        return mc != null;
    }

}
