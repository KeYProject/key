/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Size {
    /*@ public normal_behavior
      @   requires n >= 0;
      @   ensures \result == 1; @*/
    public int size(int n) {
        if (n > 5) {
            return 1;
        } else if (n > 10) {
            return 2;
        }
        return 3;
    }
}
