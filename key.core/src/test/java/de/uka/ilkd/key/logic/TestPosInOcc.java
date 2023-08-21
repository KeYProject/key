/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


public class TestPosInOcc {

    private static TermBuilder TB;

    @BeforeEach
    public void setUp() {
        TB = TacletForTests.services().getTermBuilder();
    }

    @Test
    public void testIterator() {
        Sort sort1 = new SortImpl(new Name("S1"));
        LogicVariable x = new LogicVariable(new Name("x"), sort1);
        Function f = new Function(new Name("f"), sort1, sort1);
        Function p = new Function(new Name("p"), Sort.FORMULA, sort1);


        Term[] terms = new Term[3];
        terms[0] = TB.var(x);
        terms[1] = TB.func(f, new Term[] { terms[0] });
        terms[2] = TB.func(p, new Term[] { terms[1] });

        PosInOccurrence pio =
            new PosInOccurrence(new SequentFormula(terms[2]), PosInTerm.getTopLevel(), true);

        PIOPathIterator it = pio.iterator();

        // a top-level position

        assertTrue(it.hasNext());
        assertTrue(it.next() == -1 && it.getSubTerm() == terms[2]
                && it.getPosInOccurrence().subTerm() == terms[2] && it.getChild() == -1);

        // two nodes deeper

        pio = pio.down(0).down(0);
        it = pio.iterator();

        assertTrue(it.hasNext());
        assertTrue(it.next() == 0 && it.getSubTerm() == terms[2]
                && it.getPosInOccurrence().subTerm() == terms[2] && it.getChild() == 0);

        assertTrue(it.hasNext());
        assertTrue(it.next() == 0 && it.getSubTerm() == terms[1]
                && it.getPosInOccurrence().subTerm() == terms[1] && it.getChild() == 0);

        assertTrue(it.hasNext());
        assertTrue(it.next() == -1 && it.getSubTerm() == terms[0]
                && it.getPosInOccurrence().subTerm() == terms[0] && it.getChild() == -1);

        assertFalse(it.hasNext());
    }


    @Test
    public void testReplaceConstrainedFormula() {
        Sort sort1 = new SortImpl(new Name("S1"));
        LogicVariable x = new LogicVariable(new Name("x"), sort1);
        Function c = new Function(new Name("c"), sort1, new Sort[] {});
        Function f = new Function(new Name("f"), sort1, sort1);
        Function p = new Function(new Name("p"), Sort.FORMULA, sort1);

        Term[] terms = new Term[3];
        terms[0] = TB.var(x);
        terms[1] = TB.func(f, new Term[] { terms[0] });
        terms[2] = TB.func(p, new Term[] { terms[1] });
        SequentFormula cfma = new SequentFormula(terms[2]);

        Term[] terms2 = new Term[4];
        terms2[0] = TB.func(c);
        terms2[1] = TB.func(f, new Term[] { terms2[0] });
        terms2[2] = TB.func(f, new Term[] { terms2[1] });
        terms2[3] = TB.func(p, new Term[] { terms2[2] });
        SequentFormula cfma2 = new SequentFormula(terms2[3]);

        final PosInOccurrence topPIO = new PosInOccurrence(cfma, PosInTerm.getTopLevel(), true);


        // Test without metavariables involved
        PosInOccurrence pio = topPIO.down(0);
        assertSame(pio.subTerm(), terms[1]);
        PosInOccurrence pio2 = pio.replaceConstrainedFormula(cfma);
        assertEquals(pio, pio2);
        pio = pio.replaceConstrainedFormula(cfma2);
        assertSame(pio.subTerm(), terms2[2]);
    }
}
