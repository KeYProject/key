package org.key_project;

public class Demo {
    public static int g(int a, int b) {
        return f(a, -b);
    }

    /*@ public normal_behavior
      @ ensures \result == x - y;
      @*/
    public static int f(int x, int y) {
        return x - y;
    }

}