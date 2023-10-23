/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import java.util.Arrays;

import de.uka.ilkd.key.util.HelperClassForTests;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for the origin term label
 */
class OriginTermLabelTest {
    @Test
    public void testOriginTermLabelContainingRuleNamesWithSpaces() {
        // test for issue #3286
        OriginTermLabelFactory factory = new OriginTermLabelFactory();

        OriginTermLabel label = null;
        try {
            label = factory.parseInstance(Arrays.stream(new String[] {
                "User_Interaction @ node 0 (Test Test)", "[]" }).toList(),
                HelperClassForTests.createServices());
        } catch (TermLabelException e) {
            fail(e);
        }
        assertNotNull(label, "No parser error, but also no label.");
        assertEquals(OriginTermLabel.SpecType.USER_INTERACTION, label.getOrigin().specType);
    }
}
