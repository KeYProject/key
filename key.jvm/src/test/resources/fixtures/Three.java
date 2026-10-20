/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
public class Three {

    /** A bounded javac-style {@code do {} while} loop: the body and the bottom-of-loop condition
     *  compile to straight-line code whose restart is a <em>backward</em> {@code goto}, kept by
     *  the transpiler as the backward {@code jvm.Local.goto_(pc)} call inside the L-block
     *  (loops are <em>not</em> structured — §3.4's emission is an optimization). Unlike Sum's
     *  {@code while} header, this shape needs no {@code if}-split to enter the body, so auto mode
     *  drives the loop to termination purely via {@code GotoRestoreRule} unrolling — the
     *  backward-jump analog of how {@code GotoSpliceRule} resolves forward jumps (see
     *  {@code LoopProofTest}, proof side {@code golden/Three.java}). */
    public static int sum3() {
        int s = 0;
        int i = 0;
        do { s = s + 1; i = i + 1; } while (i < 3);
        return s;
    }
}
