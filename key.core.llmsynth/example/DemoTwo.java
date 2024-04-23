package org.key_project;

public /*@ spec_safe_math @*/ class DemoTwo {
    /*@ public normal_behavior
      @ ensures \result == a + b;
      @*/
    public static int g(int a, int b) {
        return f(a, -b);
    }


    public static int f(int x, int y) {
        return x - y;
    }
}