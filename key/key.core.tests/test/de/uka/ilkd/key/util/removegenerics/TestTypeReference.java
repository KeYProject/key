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


public class TestTypeReference extends ResolveGenericClassTest {
    
    @Override
    protected void setUp() throws Exception {
        registerCU("package java.lang; class Object { }");
        registerCU("class G<E> { E m() { return null; } } interface H<E> {} class C {}");
    }

    public void testExtendsAndImplementsReference() throws Exception {
        String before = "class A extends G<C> implements H<G<C>>{ }";
        String after = "class A extends G implements H { }";
        equalCU(before, after);
    }
    
    public void testFieldType() throws Exception {
        String before = "class A { G<C> a; }";
        String after = "class A { G a; }";
        equalCU(before, after);
    }
    
    public void testLocVar() throws Exception {
        String before = "class A { void m() { G<C> a; }}";
        String after = "class A { void m() { G a; } }";
        equalCU(before, after); 
    }
    
    public void testQualifiedBound() throws Exception {
        String before = "class A<E extends java.lang.Object> { E object; }";
        String after  = "class A {\n\n java.lang.Object object; }";
        equalCU(before, after);
    }
  
    public void testConstructor() throws Exception {
        String before = "class A { void m() { new G<C>(); }}";
        String after  = "class A { void m() { new G(); } }";
        equalCU(before, after); 
    }    
    
    public void testTypeVariable() throws Exception {
        String before = "class A<E> { E field; }";
        String after  = "class A {\n\n    java.lang.Object field; }";
        equalCU(before, after); 
    }
    
    public void testTypeVariableArray() throws Exception {
        String before = "class A<E> { E[] array; }";
        String after  = "class A {\n\n    java.lang.Object[] array; }";
        equalCU(before, after); 
    }
    
    public void testCastToTV() throws Exception {
        String before = "class A<E> { E e = (E)null; }";
        String after  = "class A {java.lang.Object e = (java.lang.Object)null; }";
        equalCU(before, after); 
    }
    
    public void testVariableDeclaration() throws Exception {
        String before = "class T<E,F> { void m() { E e1; E e2=e1; n(e2); F f1; n(e2); } void n(E e) { } }";
        String after= "class T { void m() { java.lang.Object e1; java.lang.Object e2 = e1; n(e2); java.lang.Object f1; n(e2); } " +
                        "void n(java.lang.Object e) {} }";
        equalCU(before, after);
    }
    
}