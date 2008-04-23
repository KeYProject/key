package de.uka.ilkd.key.util.removegenerics;


public class TestClassDeclaration extends ResolveGenericClassTest {

    @Override
    protected void setUp() throws Exception {
        registerCU("package java.lang; class Object {}");
        registerCU("package java.lang; class Comparable<T extends Comparable<T>>  { public int compareTo(T o); }");
        registerCU("package java.lang; interface Comparator<T> { public int compare(T o1, T o2); }");
        registerCU("class C { C methodC() { return null; }}");
    }

    public void testClassDecl1() throws Exception {
        String before = "class A<E> { }";
        String after = "class A { }";
        equalCU(before, after);
    }

    public void testInterfaceDecl1() throws Exception {
        String before = "interface B<E> { }";
        String after = "interface B { }";
        equalCU(before, after);
    }

    public void testOverriddenMethods() throws Exception {
        String before = "class A<E> { E m(E e) { return null; } }" + 
            "class B extends A<C> { C m(C e) { return e.methodC(); } }";
        String after = "class A { java.lang.Object m(java.lang.Object e) { return null; } } " +  
            "class B extends A { " +
            "//--- This method has been created due to generics removal\n" +
            "  C m(java.lang.Object arg1) {  return this.m((C)arg1); } " +
            "  C m(C e) { return e.methodC(); } }";
        equalCU(before, after);
    }
    
    public void testOveriddenMethods2() throws Exception {
        String before = "class C1 { }" +
        "class C2 extends C1 { }" +
        "interface I1<E extends C1> { void m(E e); }" +
        "interface I2<E> { void m(E e); }" +
        "class D implements I1<C2>, I2<C2> { public void m(C2 e) { } }";
        
        String after = "class C1 { }" +
        "class C2 extends C1 { }" +
        "interface I1 { void m(C1 e); }" +
        "interface I2 { void m(java.lang.Object e); }" +
        "class D implements I1, I2 {  " +
        "//--- This method has been created due to generics removal\n" +
        "public void m(java.lang.Object arg1) { this.m((C2) arg1); } " +
        "//--- This method has been created due to generics removal\n" +
        "public void m(C1 arg1) { this.m((C2) arg1); }" +
        "public void m(C2 e) {} }";
        
        equalCU(before, after);

    }
    
    /* from java.util.Collections */
    public void testComparable() throws Exception {
        String before = "class ReverseComparator<T> implements Comparator<Comparable<Object>> {" +
        "   public int compare(Comparable<Object> c1, Comparable<Object> c2) { return c2.compareTo(c1); } }";
        String after = "class ReverseComparator implements Comparator { " +
        "//--- This method has been created due to generics removal\n" +
        "   public int compare(java.lang.Object arg1, java.lang.Object arg2) { return this.compare((java.lang.Comparable)arg1, (java.lang.Comparable)arg2); }"+
        "   public int compare(Comparable c1, Comparable c2) { return c2.compareTo(c1); } }";
        equalCU(before, after);
    }

}
