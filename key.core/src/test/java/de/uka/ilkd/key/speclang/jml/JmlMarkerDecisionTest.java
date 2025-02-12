/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.speclang.njml.JmlMarkerDecision;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class JmlMarkerDecisionTest {

    @Test
    public void testIsActiveJmlSpec() {
        JmlMarkerDecision dec = new JmlMarkerDecision(null);
        assertFalse(dec.isActiveJmlSpec("+ESC"));
        assertFalse(dec.isActiveJmlSpec("+a+b+c"));
        assertFalse(dec.isActiveJmlSpec("+a"));
        assertFalse(dec.isActiveJmlSpec("-key+key"));
        assertFalse(dec.isActiveJmlSpec("-"));
        assertFalse(dec.isActiveJmlSpec("+"));
        assertFalse(dec.isActiveJmlSpec("+ke y"));

        assertTrue(dec.isActiveJmlSpec("+key-a b"));
        assertTrue(dec.isActiveJmlSpec("+a+key"));
        assertTrue(dec.isActiveJmlSpec("+key"));
        assertTrue(dec.isActiveJmlSpec("+key"));
        assertTrue(dec.isActiveJmlSpec("+KEY"));
        assertTrue(dec.isActiveJmlSpec("+KEY"));
        assertTrue(dec.isActiveJmlSpec(""));
    }
}
