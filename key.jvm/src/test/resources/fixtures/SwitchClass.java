/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class SwitchClass {

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == (x == 0 ? 10 : (x == 1 || x == 2 ? 20 : 30));
      @*/
    public static int classify(int x) {
        switch (x) {
            case 0:
                return 10;
            case 1:
            case 2:
                return 20;
            default:
                return 30;
        }
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == (x == 7 ? 70 : (x == 100 ? 100 : -1));
      @*/
    public static int lookup(int x) {
        switch (x) {
            case 7:
                return 70;
            case 100:
                return 100;
            default:
                return -1;
        }
    }
}
