/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Point {

    public int x;
    public int y;

    /*@ public normal_behavior
      @   requires true;
      @   assignable x, y;
      @   ensures x == a && y == b;
      @*/
    public Point(int a, int b) {
        x = a;
        y = b;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == x + y;
      @*/
    public int sum() {
        return x + y;
    }
}
