/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Sum {

    /** A plain javac-style {@code while} loop: the loop header and body compile to a
     *  <em>backward</em> {@code goto} in bytecode, which the transpiler keeps as a backward
     *  {@code jvm.Local.goto_(pc)} call (loops are <em>not</em> structured by the transpiler —
     *  §3.4's structured emission is an optimization, not the shipped behavior). The proof side
     *  is carried by {@code GotoRestoreRule} (which auto mode applies — see {@code LoopProofTest};
     *  the draft "interactive-only" claim was wrong). */
    public static int whileSum(int n) {
        int s = 0;
        int i = 0;
        while (i < n) {
            s = s + i;
            i = i + 1;
        }
        return s;
    }
}
