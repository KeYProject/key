// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.removegenerics;


public class TestMethodDeclaration extends ResolveGenericClassTest {
    
    @Override
    protected void setUp() throws Exception {
        registerCU("package java.lang; class Object {}");
        registerCU("class G<E> { E m() { return null; }}");
        registerCU("class S { static <T> T[] mkarray() { return null; } }");
        registerCU("class C { public <T> T[] toArray(T[] array) { return null; } }");
    }
    
    public void testGenericMethod() throws Exception {
        String before = "class A { public <E> E print() { return null; } }";
        String after = "class A { public java.lang.Object print() { return null; } }";
        equalCU(before, after);
    }
    
    public void testMethod() throws Exception {
        String before = "class A<E> { public E m() { return null; } }";
        String after = "class A { public java.lang.Object m() { return null; } }";
        equalCU(before, after);
    }
    
    public void testMethodArray() throws Exception {
        String before = "class A { public <E> E[] print() { return null; } }";
        String after = "class A { public java.lang.Object[] print() { return null; } }";
        equalCU(before, after);
    }
    
    public void testReturnTypes() throws Exception {
        String before = "class A { public <T> T m(G<T> g) { return g.m(); } }";
        String after = "class A { public java.lang.Object m(G g) { return g.m(); } }";
        equalCU(before, after);
    }
    
    public void testToArray() throws Exception {
        String before = "class AL<E> { E[] data; public void m(C c) { data = c.toArray(new java.lang.Object[5]); } }";
        String after = "class AL { java.lang.Object[] data; public void m(C c) { data = c.toArray(new java.lang.Object[5]); } }";
        equalCU(before, after);
    }
 
    public void testExcplicitTV() throws Exception {
        String before = "class T { Object[] oa = S.<Object>mkarray(); }";
        String after = "class T {  Object[] oa = S.mkarray();  }";
        equalCU(before, after);
    }
 
}