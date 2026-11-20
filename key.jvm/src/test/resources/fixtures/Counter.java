/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Counter {

    /** No `<clinit>` initializer on purpose: the transpiler (and the
     *  `initialisation:disableStaticInitialisation` proof setting) treat static fields as
     *  uninitialized (0 / null); assignable state is only changed by the methods below. */
    public static int calls;

    public static Point mark;

    /*@ public normal_behavior
      @   assignable calls;
      @   ensures calls == \old(calls) + 1 && \result == calls;
      @*/
    public static int next() {
        calls = calls + 1;
        return calls;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == mark;
      @*/
    public static Point current() {
        return mark;
    }

    /*@ public normal_behavior
      @   assignable mark;
      @   ensures mark == p;
      @*/
    public static void remember(Point p) {
        mark = p;
    }
}
