// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util.removegenerics;

public class TestMultipleBounds extends ResolveGenericClassTest {
    
    @Override
    protected void setUp() throws Exception {
        registerCU("package java.lang; class Object {}");
        registerCU("class G<E> { E[][] array; E field; " + "E m() { return null; } " + "E[][] n() { return null; } } " + "class B { void mB() {} int attrB; }" 
                + "class C { void mC() {} int attrC; }");
    }

    public void testJLS1() throws Exception {
        String before = "interface I1 { void m1(); }\n" +
            "interface I2 { void m2(); }\n" + 
            "class T { <T extends I1 & I2> void test(T t) {" +
            "t.m1(); t.m2(); } }";
        String after = "interface I1 { void m1(); }\n" +
        "interface I2 { void m2(); }\n" + 
        "class T { void test(I1 t) {" +
        "t.m1(); ((I2) t).m2(); } }";
        equalCU(before, after);
    }
    
    public void testMethods() throws Exception {
        String before = "class A<E extends B&C> { E e; C c = e.mC(); B b = e.mB(); }";
        String after = "class A {\n\nB e; C c = ((C) e).mC(); B b = e.mB(); }";
        equalCU(before, after);
    }
    
    public void testAttributes() throws Exception {
        String before = "class A<E extends B&C> { E e; int i1 = e.attrB; int i2 = e.attrC; }";
        String after = "class A { B e; int i1 = e.attrB; int i2 = ((C) e).attrC; }";
        equalCU(before, after);
    }

    public void testTricky2Supertypes() throws Exception {
        String before = "class A<E extends B&C> { G<E> g = new G<E>(); C c = g.m(); B b = g.m(); }";
        String after = "class A { G g = new G(); C c = ((C) g.m()); B b = ((B) g.m()); }";
        equalCU(before, after);
    }
    
    public void testRecursiveBounds() throws Exception {
        String before = "class A<E1 extends B, E2 extends E1> { E1 e1; E2 e2; }";
        String after = "class A { B e1; B e2; }";
        equalCU(before, after);
    }
    
    public void testAsArguments() throws Exception {
        String before = "class A<E extends B&C> { abstract static void k(C c); E e; { k(e); } }";
        String after = "class A { abstract static void k(C c); B e; { k(((C)e)); }  }";
        equalCU(before, after); 
    }
    
}
