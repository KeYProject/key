/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.removegenerics;


import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

public class TestMethodDeclaration extends ResolveGenericClass {

    @BeforeEach
    protected void setUp() throws Exception {
        registerCU("package java.lang; class Object {}");
        registerCU("class G<E> { E m() { return null; }}");
        registerCU("class S { static <T> T[] mkarray() { return null; } }");
        registerCU("class C { public <T> T[] toArray(T[] array) { return null; } }");
    }

    @Test
    public void testGenericMethod() throws Exception {
        String before = "class A { public <E> E print() { return null; } }";
        String after = "class A { public java.lang.Object print() { return null; } }";
        equalCU(before, after);
    }

    @Test
    public void testMethod() throws Exception {
        String before = "class A<E> { public E m() { return null; } }";
        String after = "class A { public java.lang.Object m() { return null; } }";
        equalCU(before, after);
    }

    @Test
    public void testMethodArray() throws Exception {
        String before = "class A { public <E> E[] print() { return null; } }";
        String after = "class A { public java.lang.Object[] print() { return null; } }";
        equalCU(before, after);
    }

    @Test
    public void testReturnTypes() throws Exception {
        String before = "class A { public <T> T m(G<T> g) { return g.m(); } }";
        String after = "class A { public java.lang.Object m(G g) { return g.m(); } }";
        equalCU(before, after);
    }

    @Test
    public void testToArray() throws Exception {
        String before =
            "class AL<E> { E[] data; public void m(C c) { data = c.toArray(new java.lang.Object[5]); } }";
        String after =
            "class AL { java.lang.Object[] data; public void m(C c) { data = c.toArray(new java.lang.Object[5]); } }";
        equalCU(before, after);
    }

    @Test
    public void testExcplicitTV() throws Exception {
        String before = "class T { Object[] oa = S.<Object>mkarray(); }";
        String after = "class T {  Object[] oa = S.mkarray();  }";
        equalCU(before, after);
    }

}
