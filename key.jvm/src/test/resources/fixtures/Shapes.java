/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Shapes {

    /*@ public normal_behavior
      @   requires p != null;
      @   assignable \nothing;
      @   ensures \result == p.x + p.y;
      @*/
    public static int total(Point p) {
        return p.x + p.y;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == 3;
      @*/
    public static int make() {
        Point p = new Point(1, 2);
        return p.sum();
    }
}
