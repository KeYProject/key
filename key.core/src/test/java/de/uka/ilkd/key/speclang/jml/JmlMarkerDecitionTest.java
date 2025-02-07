/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.speclang.njml.JmlMarkerDecision;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;


public class JmlMarkerDecitionTest {

    @Test
    public void testIsActiveJmlSpec() {
        JmlMarkerDecision dec = new JmlMarkerDecision(null);
        Assertions.assertFalse(dec.isActiveJmlSpec("+ESC"));
        Assertions.assertFalse(dec.isActiveJmlSpec("+a+b+c"));
        Assertions.assertFalse(dec.isActiveJmlSpec("+a"));
        Assertions.assertFalse(dec.isActiveJmlSpec("-key+key"));
        Assertions.assertFalse(dec.isActiveJmlSpec("-"));
        Assertions.assertFalse(dec.isActiveJmlSpec("+"));
        Assertions.assertFalse(dec.isActiveJmlSpec("+ke y"));
        Assertions.assertFalse(dec.isActiveJmlSpec("+key-a b"));
        Assertions.assertTrue(dec.isActiveJmlSpec("+a+key"));
        Assertions.assertTrue(dec.isActiveJmlSpec("+key"));
        Assertions.assertTrue(dec.isActiveJmlSpec("+key"));
        Assertions.assertTrue(dec.isActiveJmlSpec("+KEY"));
        Assertions.assertTrue(dec.isActiveJmlSpec("+KEY"));
        Assertions.assertTrue(dec.isActiveJmlSpec(""));
    }
}
