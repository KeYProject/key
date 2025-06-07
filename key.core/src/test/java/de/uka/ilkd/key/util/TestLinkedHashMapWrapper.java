/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import java.util.Arrays;
import java.util.Iterator;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.SortImpl;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.Pair;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;
import static de.uka.ilkd.key.logic.equality.ProofIrrelevancyProperty.PROOF_IRRELEVANCY_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingSourceElementProperty.RENAMING_SOURCE_ELEMENT_PROPERTY;
import static de.uka.ilkd.key.logic.equality.RenamingTermProperty.RENAMING_TERM_PROPERTY;
import static de.uka.ilkd.key.logic.equality.TermLabelsProperty.TERM_LABELS_PROPERTY;
import static org.junit.jupiter.api.Assertions.*;

public class TestLinkedHashMapWrapper {
    private TermBuilder tb;

    private TermFactory tf;

    final private TermLabel relevantLabel = ParameterlessTermLabel.UNDEFINED_VALUE_LABEL;
    private static TermLabel irrelevantLabel = null;
    final private static OriginTermLabelFactory factory = new OriginTermLabelFactory();

    @BeforeAll
    public static void setIrrelevantLabel() {
        try {
            irrelevantLabel = factory.parseInstance(Arrays.stream(new String[] {
                "User_Interaction @ node 0 (Test Test)", "[]" }).toList(),
                HelperClassForTests.createServices());
        } catch (TermLabelException e) {
            fail(e);
        }
    }

    @BeforeEach
    public void setUp() {
        tb = TacletForTests.services().getTermBuilder();
        tf = TacletForTests.services().getTermFactory();
    }

    @Test
    public void testGeneralMethods() {
        // exact property does not matter for these tests
        LinkedHashMapWrapper<JTerm, Integer> wrappedMap =
            new LinkedHashMapWrapper<>(TERM_LABELS_PROPERTY);
        assertTrue(wrappedMap.isEmpty());
        assertEquals(0, wrappedMap.size());

        JTerm t1 = tb.tt();
        JTerm t2 = tb.ff();

        // add mapping t1 -> 1
        wrappedMap.put(t1, 1);
        assertEquals(1, wrappedMap.size());
        assertFalse(wrappedMap.isEmpty());
        assertTrue(wrappedMap.containsKey(t1));
        assertEquals(1, wrappedMap.get(t1));
        assertTrue(wrappedMap.containsValue(1));
        assertFalse(wrappedMap.containsValue(2));

        // add mapping t2 -> 2
        wrappedMap.put(t2, 2);
        assertEquals(2, wrappedMap.size());
        assertFalse(wrappedMap.isEmpty());
        assertTrue(wrappedMap.containsKey(t2));
        assertEquals(2, wrappedMap.get(t2));
        assertTrue(wrappedMap.containsValue(2));
        assertFalse(wrappedMap.containsValue(3));

        // remove mapping t1 -> 1
        int t1Val = wrappedMap.remove(t1);
        assertEquals(1, wrappedMap.size());
        assertFalse(wrappedMap.containsKey(t1));
        assertEquals(1, t1Val);
        assertFalse(wrappedMap.containsValue(1));

        // remove mapping t2 -> 2
        int t2Val = wrappedMap.remove(t2);
        assertEquals(0, wrappedMap.size());
        assertTrue(wrappedMap.isEmpty());
        assertFalse(wrappedMap.containsKey(t2));
        assertEquals(2, t2Val);
        assertFalse(wrappedMap.containsValue(2));
    }

    @Test
    public void testTermLabelProperties() {
        LinkedHashMap<JTerm, Integer> basicMap = new LinkedHashMap<>();
        LinkedHashMapWrapper<JTerm, Integer> termLabelsMap =
            new LinkedHashMapWrapper<>(TERM_LABELS_PROPERTY);
        LinkedHashMapWrapper<JTerm, Integer> irrelevantTermLabelsMap =
            new LinkedHashMapWrapper<>(IRRELEVANT_TERM_LABELS_PROPERTY);

        JTerm noLabelTT = tb.tt();

        JTerm irrelevantLabelTT = tb.label(noLabelTT, irrelevantLabel);
        JTerm relevantLabelTT = tb.label(noLabelTT, relevantLabel);

        // add mappings without labels to all maps
        basicMap.put(noLabelTT, 1);
        assertEquals(1, basicMap.size());

        termLabelsMap.put(noLabelTT, 1);
        assertEquals(1, termLabelsMap.size());

        irrelevantTermLabelsMap.put(noLabelTT, 1);
        assertEquals(1, irrelevantTermLabelsMap.size());

        // add mappings with irrelevant labels to all maps
        assertNull(basicMap.put(irrelevantLabelTT, 2),
            "Nothing should be returned as basicMap should not contain the key");
        assertEquals(2, basicMap.size());

        assertEquals(1, termLabelsMap.put(irrelevantLabelTT, 2),
            "Old value should be returned as termLabelsMap should already contain the key");
        assertEquals(1, termLabelsMap.size(),
            "Size should not increase as the key is already in the map");
        assertEquals(2, termLabelsMap.get(noLabelTT),
            "Checking key without label should return new value");

        assertEquals(1, irrelevantTermLabelsMap.put(irrelevantLabelTT, 2),
            "Old value should be returned as irrelevantTermLabelsMap should already contain the key");
        assertEquals(1, irrelevantTermLabelsMap.size(),
            "Size should not increase as the key is already in the map");
        assertEquals(2, irrelevantTermLabelsMap.get(irrelevantLabelTT),
            "Checking key without label should return new value");

        // add mappings with relevant labels to all maps

        assertNull(basicMap.put(relevantLabelTT, 3),
            "Nothing should be returned as basicMap should not contain the key");
        assertEquals(3, basicMap.size());

        assertEquals(2, termLabelsMap.put(relevantLabelTT, 3),
            "Value 3 should be returned as termLabelsMap was previously updated with irrelevantLabelTT");
        assertEquals(1, termLabelsMap.size(),
            "Size should not increase as the key is already in the map");
        assertEquals(3, termLabelsMap.get(noLabelTT),
            "Checking key without label should return new value");
        assertEquals(3, termLabelsMap.get(irrelevantLabelTT),
            "Checking key with irrelevant label should return new value");

        assertNull(irrelevantTermLabelsMap.put(relevantLabelTT, 3),
            "Nothing should be returned as irrelevantTermLabelsMap should not contain the key");
        assertEquals(2, irrelevantTermLabelsMap.size(),
            "Size should increase as the key is not in the map");
        assertEquals(2, irrelevantTermLabelsMap.get(irrelevantLabelTT),
            "Checking key with irrelevant label should return old value");
        assertEquals(2, irrelevantTermLabelsMap.get(noLabelTT),
            "Checking key without label should return old value");
        assertEquals(3, irrelevantTermLabelsMap.get(relevantLabelTT),
            "Checking key with relevant label should return new value");
    }

    @Test
    public void testProofIrrelevancyProperty() {
        LinkedHashMapWrapper<JTerm, Integer> proofIrrelevancyMap =
            new LinkedHashMapWrapper<>(PROOF_IRRELEVANCY_PROPERTY);

        JTerm noLabelTT = tb.tt();

        JTerm irrelevantLabelTT = tb.label(noLabelTT, irrelevantLabel);
        JTerm relevantLabelTT = tb.label(noLabelTT, relevantLabel);

        // add mapping without label
        assertNull(proofIrrelevancyMap.put(noLabelTT, 1),
            "Nothing should be returned as proofIrrelevancyMap should not contain the key");
        assertEquals(1, proofIrrelevancyMap.size());

        // add mapping with irrelevant label
        assertEquals(1, proofIrrelevancyMap.put(irrelevantLabelTT, 2),
            "Old value should be returned as irrelevantTermLabelsMap should already contain the key");
        assertEquals(1, proofIrrelevancyMap.size(),
            "Size should not increase as the key is already in the map");
        assertEquals(2, proofIrrelevancyMap.get(irrelevantLabelTT),
            "Checking key without label should return new value");

        // add mapping with relevant label
        assertNull(proofIrrelevancyMap.put(relevantLabelTT, 3),
            "Nothing should be returned as irrelevantTermLabelsMap should not contain the key");
        assertEquals(2, proofIrrelevancyMap.size(),
            "Size should increase as the key is not in the map");
        assertEquals(2, proofIrrelevancyMap.get(irrelevantLabelTT),
            "Checking key with irrelevant label should return old value");
        assertEquals(2, proofIrrelevancyMap.get(noLabelTT),
            "Checking key without label should return old value");
        assertEquals(3, proofIrrelevancyMap.get(relevantLabelTT),
            "Checking key with relevant label should return new value");;
    }

    @Test
    public void testRenamingSourceElementProperty() {
        LinkedHashMapWrapper<SourceElement, Integer> renamingSourceElementMap =
            new LinkedHashMapWrapper<>(RENAMING_SOURCE_ELEMENT_PROPERTY);

        ProgramElement match1 = TacletForTests.parsePrg("{ int i; int j; /*Test*/ }");
        ProgramElement match2 = TacletForTests.parsePrg("{ int i; /*Another test*/ int k; }");
        ProgramElement match3 = TacletForTests.parsePrg("{ int i = 3; int k; }");

        // adding { int i; int j; /*Test*/ }
        assertNull(renamingSourceElementMap.put(match1, 1));
        assertEquals(1, renamingSourceElementMap.size(), "Map should contain one element");

        // adding { int i = 3; int k; }
        assertNull(renamingSourceElementMap.put(match3, 2),
            "Nothing should be returned as the key is not in the map");
        assertEquals(2, renamingSourceElementMap.size(), "Map should contain two elements");

        // adding { int i; /*Another test*/ int k; }
        assertEquals(1, renamingSourceElementMap.put(match2, 3), "Old value should be returned");
        assertEquals(2, renamingSourceElementMap.size(), "Map should still contain two elements");
        assertEquals(3, renamingSourceElementMap.get(match1),
            "Value for match1 should be new value 3");
        assertEquals(2, renamingSourceElementMap.get(match3), "Value for match3 should be 2");
        assertEquals(3, renamingSourceElementMap.get(match2), "Value for match2 should be 3");

    }

    @Test
    public void testRenamingTermProperty() {
        LinkedHashMapWrapper<JTerm, Integer> renamingTermMap =
            new LinkedHashMapWrapper<>(RENAMING_TERM_PROPERTY);
        final Sort sort = new SortImpl(new Name("sort"));
        final LogicVariable x = new LogicVariable(new Name("x"), sort);
        final LogicVariable y = new LogicVariable(new Name("y"), sort);
        final JTerm tx = tf.createTerm(x);
        final JTerm ty = tf.createTerm(y);
        final Function f = new JFunction(new Name("f"), JavaDLTheory.FORMULA, sort, sort);
        final JTerm t1 = tb.all(x, tf.createTerm(f, tx, tx));
        final JTerm t2 = tb.all(y, tf.createTerm(f, ty, ty));
        final JTerm t3 = tb.all(y, tf.createTerm(f, ty, tx));

        // adding \forall x. x && x
        assertEquals(0, renamingTermMap.size(), "Map should be empty");
        renamingTermMap.put(t1, 1);
        assertEquals(1, renamingTermMap.size(), "Map should contain one element");

        // adding \forall y. y && y
        assertEquals(1, renamingTermMap.put(t2, 2), "Old value should be returned");
        assertEquals(1, renamingTermMap.size(), "Map should still contain one element");
        assertTrue(renamingTermMap.containsKey(t1),
            "As renaming is ignored, t1 should be in the map");
        assertTrue(renamingTermMap.containsKey(t2),
            "As renaming is ignored, t2 should be in the map");

        // adding \forall y. y && x
        assertNull(renamingTermMap.put(t3, 3),
            "Nothing should be returned as the key is not in the map");
        assertEquals(2, renamingTermMap.size(), "Map should contain two elements");
        assertEquals(2, renamingTermMap.get(t1), "Value for t1 should be 2");
        assertEquals(2, renamingTermMap.get(t2), "Value for t2 should be 2");
        assertEquals(3, renamingTermMap.get(t3), "Value for t3 should be 3");
    }

    @Test
    public void testConstructors() {
        LinkedHashMapWrapper<JTerm, Integer> wrappedMap =
            new LinkedHashMapWrapper<JTerm, Integer>(tb.tt(), 1, TERM_LABELS_PROPERTY);
        assertFalse(wrappedMap.isEmpty(), "Map should not be empty (0)");
        assertEquals(1, wrappedMap.size(), "Map should contain one element");
        assertTrue(wrappedMap.containsKey(tb.tt()), "Map should contain key tt");

        // putAll is also tested with these constructor calls
        LinkedHashMapWrapper<JTerm, Integer> wrappedMap2 =
            new LinkedHashMapWrapper<JTerm, Integer>(new JTerm[] { tb.tt(), tb.ff() },
                new Integer[] { 1, 2 },
                TERM_LABELS_PROPERTY);
        assertFalse(wrappedMap2.isEmpty(), "Map should not be empty (1)");
        assertEquals(2, wrappedMap2.size(), "Map should contain two elements");

        LinkedHashMapWrapper<JTerm, Integer> wrappedMap3 =
            new LinkedHashMapWrapper<>(new ImmutableArray<>(tb.tt(), tb.ff(), tb.tt()),
                new ImmutableArray<>(1, 2, 3),
                TERM_LABELS_PROPERTY);
        assertFalse(wrappedMap3.isEmpty(), "Map should not be empty (2)");
        assertEquals(2, wrappedMap3.size(), "Map should contain two elements, as tt is repeated");
        assertFalse(wrappedMap3.containsValue(1),
            "Map should not contain value 1 as it should be overwritten by 3");

        Iterator<Pair<JTerm, Integer>> it1 = wrappedMap3.iterator();
        it1.forEachRemaining(pair -> {
            if (pair.first.equals(tb.tt())) {
                assertEquals(3, pair.second, "Value for tt should be 3");
            } else if (pair.first.equals(tb.ff())) {
                assertEquals(2, pair.second, "Value for ff should be 2");
            } else {
                fail("Unexpected key in map");
            }
        });

        Iterator<Pair<JTerm, Integer>> it2 = wrappedMap2.iterator();
        assertTrue(it2.hasNext(), "Iterator should have next element");
        it2.next();
        assertTrue(it2.hasNext(), "Iterator should have next element");
        it2.next();
        assertFalse(it2.hasNext(), "Iterator should not have next element");
    }
}
