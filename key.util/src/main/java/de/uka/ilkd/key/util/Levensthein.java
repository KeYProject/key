/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.util.*;


/// Calculates the Levensthein distance between two strings, also known as the minimal editing
/// distance.
/// This is a classical approach done in Dynamic Programming.
/// [Code taken from Baeldung](https://www.baeldung.com/java-levenshtein-distance)
public class Levensthein {
    public static int calculate(String x, String y) {
        int[][] dp = new int[x.length() + 1][y.length() + 1];
        for (int i = 0; i <= x.length(); i++) {
            for (int j = 0; j <= y.length(); j++) {
                if (i == 0) {
                    dp[i][j] = j;
                } else if (j == 0) {
                    dp[i][j] = i;
                } else {
                    dp[i][j] = min(
                        dp[i - 1][j - 1] + costOfSubstitution(x.charAt(i - 1), y.charAt(j - 1)),
                        dp[i - 1][j] + 1,
                        dp[i][j - 1] + 1);
                }
            }
        }
        return dp[x.length()][y.length()];
    }

    private static int costOfSubstitution(char a, char b) {
        return a == b ? 0 : 1;
    }

    private static int min(int a, int b, int c) {
        return Math.min(a, Math.min(b, c));
    }

    /// Creates a Heap data structure, which is sorted by similarness to the given String [fixed].
    /// @return {@link PriorityQueue} where the first element is the most similar element to
    /// [fixed].
    public static PriorityQueue<String> findSimilarNames(String fixed, Collection<String> names) {
        Map<String, Integer> map = new HashMap<>();
        for (var name : names) {
            map.put(name, calculate(name, fixed));
        }
        var comparator = Comparator.comparing(map::get);
        PriorityQueue<String> pq = new PriorityQueue<>(comparator);
        pq.addAll(map.keySet());
        return pq;
    }
}
