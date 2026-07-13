public class InnerCls {
    int base = 5;
    class Inner { int get() { return base; } }
    int f() { Inner i = new InnerCls().new Inner(); return i.get(); }
}
