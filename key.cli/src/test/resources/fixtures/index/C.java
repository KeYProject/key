/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class C {
    /*@ public normal_behavior
      @   ensures \result == 1; @*/
    public int one() {
        return 1;
    }

    /*@ public normal_behavior
      @   ensures \result == 1; @*/
    public int two() {
        return 2;
    }
}
