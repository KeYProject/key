/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;


import java.util.Arrays;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.TacletForTests;

import org.key_project.util.collection.ImmutableArray;

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

    final private TermLabel relevantLabel1 = ParameterlessTermLabel.UNDEFINED_VALUE_LABEL;
    final private TermLabel relevantLabel2 = ParameterlessTermLabel.SHORTCUT_EVALUATION_LABEL;
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
        LinkedHashMapWrapper<Term, Integer> wrappedMap =
            new LinkedHashMapWrapper<>(TERM_LABELS_PROPERTY);
        assertTrue(wrappedMap.isEmpty());
        assertEquals(0, wrappedMap.size());

        Term t1 = tb.tt();
        Term t2 = tb.ff();

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
        LinkedHashMap<Term, Integer> basicMap = new LinkedHashMap<>();
        LinkedHashMapWrapper<Term, Integer> termLabelsMap =
            new LinkedHashMapWrapper<>(TERM_LABELS_PROPERTY);
        LinkedHashMapWrapper<Term, Integer> irrelevantTermLabelsMap =
            new LinkedHashMapWrapper<>(IRRELEVANT_TERM_LABELS_PROPERTY);

        Term noLabelTT = tb.tt();
        Term noLabelFF = tb.ff();

        Term irrelevantLabelTT = tb.label(noLabelTT, irrelevantLabel);
        Term irrelevantLabelFF = tb.label(noLabelFF, irrelevantLabel);
        Term relevantLabelTT = tb.label(noLabelTT, relevantLabel1);
        Term relevantLabelFF = tb.label(noLabelFF, relevantLabel2);

        // add mappings without labels to all maps
        basicMap.put(noLabelTT, 1);
        basicMap.put(noLabelFF, 2);
        assertEquals(2, basicMap.size());

        termLabelsMap.put(noLabelTT, 1);
        termLabelsMap.put(noLabelFF, 2);
        assertEquals(2, termLabelsMap.size());

        irrelevantTermLabelsMap.put(noLabelTT, 1);
        irrelevantTermLabelsMap.put(noLabelFF, 2);
        assertEquals(2, irrelevantTermLabelsMap.size());

        // add mappings with irrelevant labels to all maps
        assertNull(basicMap.put(irrelevantLabelTT, 3), "Nothing should be returned as basicMap should not contain the key");
        assertEquals(3, basicMap.size());

        assertEquals(1, termLabelsMap.put(irrelevantLabelTT, 3), "Old value should be returned as termLabelsMap should already contain the key");
        assertEquals(2, termLabelsMap.size(), "Size should not increase as the key is already in the map");
        assertEquals(3, termLabelsMap.get(noLabelTT), "Checking key without label should return new value");

        assertEquals(1, irrelevantTermLabelsMap.put(irrelevantLabelTT, 3), "Old value should be returned as irrelevantTermLabelsMap should already contain the key");
        assertEquals(2, irrelevantTermLabelsMap.size(), "Size should not increase as the key is already in the map");
        assertEquals(3, irrelevantTermLabelsMap.get(irrelevantLabelTT), "Checking key without label should return new value");

        // add mappings with relevant labels to all maps

        assertNull(basicMap.put(relevantLabelTT, 4), "Nothing should be returned as basicMap should not contain the key");
        assertEquals(4, basicMap.size());

        assertEquals(3, termLabelsMap.put(relevantLabelTT, 4), "Value 3 should be returned as termLabelsMap was previously updated with irrelevantLabelTT");
        assertEquals(3, termLabelsMap.size(), "Size should not increase as the key is already in the map");
        assertEquals(4, termLabelsMap.get(noLabelTT), "Checking key without label should return new value");
        assertEquals(4, termLabelsMap.get(irrelevantLabelTT), "Checking key with irrelevant label should return new value");


    }

    @Test
    public void testProofIrrelevancyProperty() {
        LinkedHashMapWrapper<Term, Integer> ProofIrrelevancyMap =
            new LinkedHashMapWrapper<>(PROOF_IRRELEVANCY_PROPERTY);

    }

    @Test
    public void testRenamingTermProperty() {
        LinkedHashMapWrapper<Term, Integer> renamingTermMap =
            new LinkedHashMapWrapper<>(RENAMING_TERM_PROPERTY);

    }

    @Test
    public void testRenamingSourceElementProperty() {
        LinkedHashMapWrapper<SourceElement, Integer> renamingSourceElementMap =
                new LinkedHashMapWrapper<>(RENAMING_SOURCE_ELEMENT_PROPERTY);
        LinkedHashMap<SourceElement, Integer> basicMap = new LinkedHashMap<>();


    }

    @Test
    public void testConstructors() {
        LinkedHashMapWrapper<Term, Integer> wrappedMap =
                new LinkedHashMapWrapper<>(tb.tt(), 1, TERM_LABELS_PROPERTY);
        assertFalse(wrappedMap.isEmpty());
        assertEquals(1, wrappedMap.size());
        assertTrue(wrappedMap.containsKey(tb.tt()));

        // putAll is also tested with these constructor calls
    }

    @Test
    public void testSpecialCases() {

    }
}
