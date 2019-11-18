// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.HashSet;
import java.util.Set;

import junit.framework.TestCase;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.taclettranslation.TacletFormula;

public class TestGenericRemovingLemmaGenerator extends TestCase {

    public void testRemovingGenericSorts() {

        TacletForTests.parse();
        NoPosTacletApp app = TacletForTests.getRules().lookup(new Name("TestRemovingGenericSorts"));

        GenericRemovingLemmaGenerator g = new GenericRemovingLemmaGenerator();
        TacletFormula result = g.translate(app.taclet(), TacletForTests.services());

        Set<Sort> sorts = new HashSet<Sort>();
        collectSorts(result.getFormula(TacletForTests.services()), sorts);

        Name nameG = new Name("G");
        boolean found = false;
        for (Sort sort : sorts) {
            assertFalse("No generic sorts must survive", sort instanceof GenericSort);

            if(!found && sort instanceof ProxySort && sort.name().equals(nameG)) {
                found = true;
            }
        }
        assertTrue("There is a proxy sort of the name 'G'", found);
    }

    private void collectSorts(Term term, Set<Sort> sorts) {
        for (Term t : term.subs()) {
            collectSorts(t, sorts);
        }

        sorts.add(term.sort());

        if (term.op() instanceof SortDependingFunction){
            SortDependingFunction sdf = (SortDependingFunction) term.op();
            sorts.add(sdf.getSortDependingOn());
        }

        for (QuantifiableVariable v : term.boundVars()) {
            sorts.add(v.sort());
        }
    }
}