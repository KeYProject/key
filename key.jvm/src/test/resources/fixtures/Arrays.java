/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Arrays {

    /*@ public normal_behavior
      @   requires a != null;
      @   assignable \nothing;
      @   ensures \result == a.length;
      @*/
    public static int length(int[] a) {
        return a.length;
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable \nothing;
      @   ensures \result == a[i];
      @*/
    public static int at(int[] a, int i) {
        return a[i];
    }

    /*@ public normal_behavior
      @   requires a != null && 0 <= i && i < a.length;
      @   assignable a[i];
      @   ensures a[i] == v;
      @*/
    public static void set(int[] a, int i, int v) {
        a[i] = v;
    }

    /*@ public normal_behavior
      @   requires 0 <= n;
      @   assignable \nothing;
      @   ensures \result != null && \result.length == n;
      @*/
    public static int[] make(int n) {
        return new int[n];
    }
}
