/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Caster {

    /*@ public normal_behavior
      @   requires o instanceof Point;
      @   assignable \nothing;
      @   ensures \result == o;
      @*/
    public static Point asPoint(Object o) {
        return (Point) o;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == (o instanceof Point ? 1 : 0);
      @*/
    public static int classify(Object o) {
        if (o instanceof Point) {
            return 1;
        } else {
            return 0;
        }
    }
}
