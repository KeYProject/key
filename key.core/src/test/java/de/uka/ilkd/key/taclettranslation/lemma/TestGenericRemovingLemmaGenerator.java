/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.HashSet;
import java.util.Set;

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

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class TestGenericRemovingLemmaGenerator {
    @Test
    public void testRemovingGenericSorts() {
        TacletForTests.parse();
        NoPosTacletApp app = TacletForTests.getRules().lookup(new Name("TestRemovingGenericSorts"));
        Assertions.assertNotNull(app);

        GenericRemovingLemmaGenerator g = new GenericRemovingLemmaGenerator();
        TacletFormula result = g.translate(app.taclet(), TacletForTests.services());

        Set<Sort> sorts = new HashSet<>();
        collectSorts(result.getFormula(TacletForTests.services()), sorts);

        Name nameG = new Name("G");
        boolean found = false;
        for (Sort sort : sorts) {
            Assertions.assertFalse(sort instanceof GenericSort, "No generic sorts must survive");

            if (!found && sort instanceof ProxySort && sort.name().equals(nameG)) {
                found = true;
            }
        }
        Assertions.assertTrue(found, "There is a proxy sort of the name 'G'");
    }

    private void collectSorts(Term term, Set<Sort> sorts) {
        for (Term t : term.subs()) {
            collectSorts(t, sorts);
        }

        sorts.add(term.sort());

        if (term.op() instanceof SortDependingFunction) {
            SortDependingFunction sdf = (SortDependingFunction) term.op();
            sorts.add(sdf.getSortDependingOn());
        }

        for (QuantifiableVariable v : term.boundVars()) {
            sorts.add(v.sort());
        }
    }
}
