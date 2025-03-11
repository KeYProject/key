/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableArray;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class LabelCollectionTest {

    private LabelCollection collection;
    private ParameterlessTermLabel paramA;
    private ParameterlessTermLabel paramB;
    private FormulaTermLabel formulaLabel;

    @BeforeEach
    void setup() {
        paramA = new ParameterlessTermLabel(new Name("A"));
        paramB = new ParameterlessTermLabel(new Name("B"));
        try {
            formulaLabel = new FormulaTermLabel("10.5");
        } catch (TermLabelException e) {
            throw new RuntimeException(e);
        }
        final TermLabel[] labels = new TermLabel[] {
            paramA,
            formulaLabel,
            paramB,
        };
        this.collection = new LabelCollection(new ImmutableArray<>(labels));
    }


    @Test
    void addSuccess() {
        assertFalse(collection.isModified(), "Initial collection should not be marked as modified");
        final int oldSize = collection.getLabels().size();
        ParameterlessTermLabel label = new ParameterlessTermLabel(new Name("C"));
        collection.add(label);
        assertTrue(collection.isModified());
        assertTrue(collection.contains(label));
        assertTrue(collection.getLabels().size() == oldSize + 1);
    }

    void addFail() {
        assertFalse(collection.isModified(), "Initial collection should not be marked as modified");
        final int oldSize = collection.getLabels().size();
        collection.add(paramA);
        assertFalse(collection.isModified());
        assertTrue(collection.contains(paramA));
        assertTrue(collection.getLabels().size() == oldSize);
    }

    @Test
    void removeSuccess() {
        assertFalse(collection.isModified(), "Initial collection should not be marked as modified");

        final int oldSize = collection.getLabels().size();
        collection.remove(paramB);
        assertTrue(collection.isModified());
        assertFalse(collection.contains(paramB));
        assertTrue(collection.getLabels().size() == oldSize - 1);
    }

    @Test
    void removeFail() {
        assertFalse(collection.isModified(), "Initial collection should not be marked as modified");

        final int oldSize = collection.getLabels().size();
        ParameterlessTermLabel label = new ParameterlessTermLabel(new Name("C"));
        assertFalse(collection.contains(label));
        collection.remove(label);
        assertFalse(collection.isModified());
        assertFalse(collection.contains(label));
        assertTrue(collection.getLabels().size() == oldSize);
    }

    @Test
    void removeIfSuccess() {
        assertFalse(collection.isModified(), "Initial collection should not be marked as modified");

        final int oldSize = collection.getLabels().size();
        collection.removeIf(l -> l.getClass() == ParameterlessTermLabel.class);
        assertTrue(collection.isModified());
        assertFalse(collection.contains(paramA));
        assertFalse(collection.contains(paramB));
        assertTrue(collection.getLabels().size() == oldSize - 2);
    }

    @Test
    void removeIfFail() {
        assertFalse(collection.isModified(), "Initial collection should not be marked as modified");

        final int oldSize = collection.getLabels().size();
        ParameterlessTermLabel label = new ParameterlessTermLabel(new Name("C"));
        assertFalse(collection.contains(label));
        collection.removeIf(l -> l.name().toString().equals("C"));
        assertFalse(collection.isModified());
        assertFalse(collection.contains(label));
        assertTrue(collection.getLabels().size() == oldSize);
    }

    @Test
    void getFirst() {
        assertFalse(collection.isModified(), "Initial collection should not be marked as modified");
        assertEquals(collection.getFirst(ParameterlessTermLabel.class), paramA);
    }
}
