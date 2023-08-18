/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import java.util.Arrays;
import java.util.Set;
import java.util.TreeSet;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.speclang.jml.JMLUtils.isJmlCommentStarter;
import static de.uka.ilkd.key.speclang.jml.JMLUtils.splitJmlMarker;
import static org.junit.jupiter.api.Assertions.assertEquals;

@Deprecated
public class JMLUtilsTest {

    @Test
    public void testSplitJmlFeatures() {
        assertEquals(treeSet("+key", "+openjml"), splitJmlMarker("+key+openjml@"));
        assertEquals(treeSet("+key", "+openjml"), splitJmlMarker("+key+openjml"));
        assertEquals(treeSet("+key", "-openjml"), splitJmlMarker("+key-openjml@"));
        assertEquals(treeSet("-key", "+esc"), splitJmlMarker("-key+ESC@"));
        assertEquals(treeSet("+key"), splitJmlMarker("+key@"));
        assertEquals(treeSet("+"), splitJmlMarker("+"));
        assertEquals(treeSet("-"), splitJmlMarker("-"));
        assertEquals(treeSet("-a", "+b"), splitJmlMarker("-a-a-a-a-a+b"));
        assertEquals(treeSet("key"), splitJmlMarker("key"));
        assertEquals(treeSet("+abc_def"), splitJmlMarker("+ABC_DEF@"));
        Assertions.assertTrue(splitJmlMarker("").isEmpty());
    }

    private Set<String> treeSet(String... s) {
        return new TreeSet<>(Arrays.asList(s));
    }

    @Test
    public void testIsJmlCommentStarter() {
        Assertions.assertFalse(isJmlCommentStarter("//+ESC@ ensures true;"));
        Assertions.assertFalse(isJmlCommentStarter("+a@+key"));
        Assertions.assertFalse(isJmlCommentStarter("//+a+b+c@ ensures true;"));
        Assertions.assertFalse(isJmlCommentStarter("/*+a"));
        Assertions.assertFalse(isJmlCommentStarter("+a"));
        Assertions.assertFalse(isJmlCommentStarter("-key+key"));
        Assertions.assertFalse(isJmlCommentStarter("-"));
        Assertions.assertFalse(isJmlCommentStarter("+"));
        Assertions.assertFalse(isJmlCommentStarter("+ke y"));
        Assertions.assertFalse(isJmlCommentStarter("+key-a b@"));
        Assertions.assertTrue(isJmlCommentStarter("+a+key"));
        Assertions.assertTrue(isJmlCommentStarter("+key"));
        Assertions.assertTrue(isJmlCommentStarter("//+key@ blubb"));
        Assertions.assertTrue(isJmlCommentStarter("//+KEY@ blubb"));
        Assertions.assertTrue(isJmlCommentStarter("/*+KEY@ blubb"));
        Assertions.assertTrue(isJmlCommentStarter("@ ensures true"));
        Assertions.assertTrue(isJmlCommentStarter("//@ ensures true"));
        Assertions.assertTrue(isJmlCommentStarter(""));
    }
}
