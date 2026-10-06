/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import org.key_project.logic.Name;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class TestName {
    @Test
    public void testEquals() {
        Name n = new Name("test");
        Name m = new Name("test");
        assertEquals(n, m);
    }
}
