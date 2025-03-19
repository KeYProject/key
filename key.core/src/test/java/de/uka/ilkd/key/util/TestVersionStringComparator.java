/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class TestVersionStringComparator {

    @Test
    public void test0() {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("1.9.3777", "2.4.0");
        assertTrue(r > 0);
    }

    @Test
    public void test1() {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("2.4.0", "2.4.0");
        assertEquals(0, r);
    }

    @Test
    public void test2() {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("not a number", "2.4.0");
        assertTrue(r > 0);
    }

    @Test
    public void test3() {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("2.4-special", "2.4.1");
        assertTrue(r > 0);
    }

    @Test
    public void test4() {
        final VersionStringComparator vsc = new VersionStringComparator();
        int r = vsc.compare("1-9$3777", "2/4*0");
        assertTrue(r > 0);
    }
}
