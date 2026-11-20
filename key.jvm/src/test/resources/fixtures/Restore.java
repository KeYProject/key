/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Restore {

    /** An infinite {@code do {} while (true)} body: javac emits a straight-line body ending in a
     *  <em>backward</em> {@code goto}, which the transpiler keeps as {@code jvm.Local.goto_(pc)}
     *  — the loop body has no branch, so {@code GotoRestoreRule} unrolls it under auto mode
     *  without a header split. The loop cannot terminate, so the proof cannot close; KeY's
     *  repeated-state anti-looping bounds the unrolling and the residual goals stay open (see
     *  {@code LoopProofTest}). */
    public static int spin() {
        int s = 0;
        do { s = s + 1; } while (true);
    }
}
