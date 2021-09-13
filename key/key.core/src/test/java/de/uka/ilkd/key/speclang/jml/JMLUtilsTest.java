package de.uka.ilkd.key.speclang.jml;

import junit.framework.TestCase;
import org.junit.Assert;

import java.util.Arrays;
import java.util.Set;
import java.util.TreeSet;

import static de.uka.ilkd.key.speclang.jml.JMLUtils.isJmlCommentStarter;
import static de.uka.ilkd.key.speclang.jml.JMLUtils.splitJmlMarker;

public class JMLUtilsTest extends TestCase {

    public void testSplitJmlFeatures() {
        Assert.assertEquals(
                treeSet("+key", "+openjml"),
                splitJmlMarker("+key+openjml@"));
        Assert.assertEquals(
                treeSet("+key", "+openjml"),
                splitJmlMarker("+key+openjml"));
        Assert.assertEquals(
                treeSet("+key", "-openjml"),
                splitJmlMarker("+key-openjml@"));
        Assert.assertEquals(
                treeSet("-key", "+esc"),
                splitJmlMarker("-key+ESC@"));
        Assert.assertEquals(
                treeSet("+key"),
                splitJmlMarker("+key@"));
        Assert.assertEquals(
                treeSet("+"),
                splitJmlMarker("+"));
        Assert.assertEquals(
                treeSet("-"),
                splitJmlMarker("-"));
        Assert.assertEquals(
                treeSet("-a", "+b"),
                splitJmlMarker("-a-a-a-a-a+b"));
        Assert.assertEquals(
                treeSet("key"),
                splitJmlMarker("key"));
        Assert.assertEquals(
                treeSet("+abc_def"),
                splitJmlMarker("+ABC_DEF@"));
        Assert.assertTrue(
                splitJmlMarker("").isEmpty());
    }

    private Set<String> treeSet(String... s) {
        return new TreeSet<>(Arrays.asList(s));
    }

    public void testIsJmlCommentStarter() {
        assertFalse(isJmlCommentStarter("//+ESC@ ensures true;"));
        assertFalse(isJmlCommentStarter("+a@+key"));
        assertFalse(isJmlCommentStarter("//+a+b+c@ ensures true;"));
        assertFalse(isJmlCommentStarter("/*+a"));
        assertFalse(isJmlCommentStarter("+a"));
        assertFalse(isJmlCommentStarter("-key+key"));
        assertFalse(isJmlCommentStarter("-"));
        assertFalse(isJmlCommentStarter("+"));
        assertFalse(isJmlCommentStarter("+ke y"));
        assertFalse(isJmlCommentStarter("+key-a b@"));
        assertTrue(isJmlCommentStarter("+a+key"));
        assertTrue(isJmlCommentStarter("+key"));
        assertTrue(isJmlCommentStarter("//+key@ blubb"));
        assertTrue(isJmlCommentStarter("//+KEY@ blubb"));
        assertTrue(isJmlCommentStarter("/*+KEY@ blubb"));
        assertTrue(isJmlCommentStarter("@ ensures true"));
        assertTrue(isJmlCommentStarter("//@ ensures true"));
        assertTrue(isJmlCommentStarter(""));
    }
}