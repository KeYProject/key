/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;


/**
 * This class provides a simple routine that performs line wrapping of strings that may contain long
 * lines.
 *
 * It is an interesting class since it is the first algorithm in KeY that has been proved correct
 * with KeY.
 *
 * It has been verified with KeY 3d4189d9107dc7df50d0fce8f45cfd02cb20ba22. Required heavy use of the
 * (then) new SMT translation. (Z3 version 4.8.8)
 *
 * @author Mattias Ulbrich, Mar 2021
 */
public class WrapUtils {

    /*
     * @ public normal_behaviour
     *
     * @ requires length > 0;
     *
     * @
     *
     * @ // This method only replaces ' ' by '\n'.
     *
     * @ ensures (\forall int i; 0 <= i && i < s.length;
     *
     * @ s[i] == \old(s[i]) || \old(s[i]) == ' ' && s[i] == '\n');
     *
     * @
     *
     * @ // If there are more than length characters w/o linebreak,
     *
     * @ // then they are all different from space
     *
     * @ ensures (\forall int i; 0 <= i && i < s.length - length;
     *
     * @ (\forall int j; i <= j && j <= i + length; s[j] != '\n')
     *
     * @ ==> (\forall int j; i <= j && j <= i + length; s[j] != ' '));
     *
     * @
     *
     * @ // Any line but the last line cannot be made any longer
     *
     * @ ensures (\forall int a,b,c; 0 <= a && a < b && b < c && c < s.length &&
     *
     * @ (a == -1 || s[a] == '\n') &&
     *
     * @ s[b] == '\n' && \old(s[b]) == ' ' &&
     *
     * @ (s[c] == ' ' || s[c] == '\n');
     *
     * @ c - a > length);
     *
     * @
     *
     * @ assignable s[*];
     *
     * @
     */
    public static void wrapLines(char[] s, int length) {

        int lastChange = -1;
        int lastSpace = -1;

        /*
         * @ loop_invariant -1 <= lastSpace && lastSpace < s.length;
         *
         * @ loop_invariant -1 <= lastChange && lastChange <= lastSpace;
         *
         * @ loop_invariant lastSpace <= lastChange + length + 1;
         *
         * @ loop_invariant lastSpace >= 0 ==>
         *
         * @ \old(s[lastSpace]) == ' ' || \old(s[lastSpace]) == '\n';
         *
         * @ loop_invariant (\forall int i; 0 <= i && i < s.length;
         *
         * @ s[i] == \old(s[i]) || \old(s[i]) == ' ' && s[i] == '\n');
         *
         * @ loop_invariant (\forall int i; 0 <= i && i < lastChange && i < s.length - length;
         *
         * @ (\forall int j; i <= j && j <= i + length; s[j] != '\n')
         *
         * @ ==> (\forall int j; i <= j && j <= i + length; s[j] != ' '));
         *
         * @ loop_invariant (\forall int a,b,c; 0 <= a && a < b && b < c && c < s.length &&
         *
         * @ b <= lastChange &&
         *
         * @ (a == -1 || s[a] == '\n') &&
         *
         * @ s[b] == '\n' && \old(s[b]) == ' ' &&
         *
         * @ (s[c] == ' ' || s[c] == '\n');
         *
         * @ c - a > length);
         *
         * @ loop_invariant (\forall int x; lastChange < x && x <= lastSpace; s[x] != '\n');
         *
         * @ loop_invariant (\forall int x; lastChange < x && x < s.length; s[x] == \old(s[x]));
         *
         * @ loop_invariant lastChange == -1 || s[lastChange] == '\n';
         *
         * @ decreases 2*s.length - lastSpace - lastChange;
         *
         * @ assignable s[*];
         *
         * @
         */
        while (true) {
            int nextSpace = indexOf(s, ' ', lastSpace + 1);
            int nextNewLine = indexOf(s, '\n', lastSpace + 1);
            if (nextSpace == -1) {
                if (s.length - lastChange > length
                        && (nextNewLine - lastChange > length || nextNewLine == -1)
                        && lastSpace >= 0) {
                    s[lastSpace] = '\n';
                }
                return;
            }

            if (0 <= nextNewLine && nextNewLine < nextSpace) {
                if (nextNewLine - lastChange > length && lastSpace >= 0) {
                    s[lastSpace] = '\n';
                }
                lastChange = lastSpace = nextNewLine;
            } else {
                if (nextSpace - lastChange > length) {
                    if (lastChange == lastSpace) {
                        s[nextSpace] = '\n';
                        lastChange = lastSpace = nextSpace;
                    } else {
                        s[lastSpace] = '\n';
                        lastChange = lastSpace;
                    }
                } else {
                    lastSpace = nextSpace;
                }
            }
        }
    }

    /*
     * @ private normal_behaviour
     *
     * @ requires 0 <= from && from <= s.length;
     *
     * @ ensures -1 == \result || from <= \result && \result < s.length;
     *
     * @ ensures \result == -1 ==>
     *
     * @ (\forall int i; from <= i && i < s.length; s[i] != c);
     *
     * @ ensures \result >= 0 ==>
     *
     * @ s[\result] == c &&
     *
     * @ (\forall int i; from <= i && i < \result; s[i] != c);
     *
     * @ assignable \strictly_nothing;
     *
     * @
     */
    private static /* @ helper */ int indexOf(char[] s, char c, int from) {
        /*
         * @ loop_invariant from <= k && k <= s.length;
         *
         * @ loop_invariant (\forall int i; from <= i && i < k; s[i] != c);
         *
         * @ decreases s.length - k;
         *
         * @ assignable \strictly_nothing;
         *
         * @
         */
        for (int k = from; k < s.length; k++) {
            if (s[k] == c) {
                return k;
            }
        }
        return -1;
    }
}
