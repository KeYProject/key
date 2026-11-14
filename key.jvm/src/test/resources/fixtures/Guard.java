/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Guard {

    /*@ public normal_behavior
      @   requires g != null;
      @   assignable \nothing;
      @   ensures \result == g.score;
      @*/
    public static int score(Gadget g) {
        return g.score;
    }

    /*@ public normal_behavior
      @   requires g != null;
      @   assignable g.score;
      @   ensures g.score == s;
      @*/
    public static void stamp(Gadget g, int s) {
        g.score = s;
    }

    /*@ public normal_behavior
      @   requires g != null;
      @   assignable \nothing;
      @   ensures \result == g.score + g.size();
      @*/
    public static int total(Gadget g) {
        return g.score + g.size();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == Gadget.kind;
      @*/
    public static int kind() {
        return Gadget.kind;
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result == Gadget.defaultScore();
      @*/
    public static int def() {
        return Gadget.defaultScore();
    }

    /*@ public normal_behavior
      @   assignable \nothing;
      @   ensures \result != null;
      @*/
    public static Gadget fresh() {
        return new Gadget();
    }
}
