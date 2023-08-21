/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.proofdiff;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.Triple;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.19)
 */
public class ProofDifference {
    private static final Integer THRESHOLD = 25;
    private List<String> leftAntec = new LinkedList<>(), rightAntec = new LinkedList<>(),
            rightSucc = new LinkedList<>(), leftSucc = new LinkedList<>();

    private final Set<String> exclusiveAntec = new HashSet<>();
    private final Set<String> commonSucc = new HashSet<>();
    private final Set<String> exclusiveSucc = new HashSet<>();
    private final Set<String> commonAntec = new HashSet<>();

    public static ProofDifference create(Services services, Node left, Node right) {
        return create(left, right, (Term t) -> LogicPrinter.quickPrintTerm(t, services));
    }

    public static ProofDifference create(Node left, Node right, Function<Term, String> printer) {
        ProofDifference pd = new ProofDifference();
        assert left != null && right != null;
        pd.leftAntec = initialise(printer, left.sequent().antecedent());
        pd.leftSucc = initialise(printer, left.sequent().succedent());
        pd.rightAntec = initialise(printer, right.sequent().antecedent());
        pd.rightSucc = initialise(printer, right.sequent().succedent());
        pd.computeDiff();
        return pd;
    }

    private static List<String> initialise(Function<Term, String> printer,
            Semisequent semisequent) {
        return semisequent.asList().stream().map(it -> printer.apply(it.formula()))
                .collect(Collectors.toList());
    }

    private static Collection<? extends String> intersect(Set<String> left, Set<String> right) {
        Set<String> intersection = new TreeSet<>(left);
        intersection.retainAll(right);
        return intersection;
    }

    private static void computeDiff(List<String> left, List<String> right, Set<String> common,
            Set<String> exclusive) {
        computeDiff(new HashSet<>(left), new HashSet<>(right), common, exclusive);
    }

    private static void computeDiff(Set<String> left, Set<String> right, Set<String> common,
            Set<String> exclusive) {
        common.addAll(intersect(left, right));
        exclusive.addAll(left);
        exclusive.addAll(right);
        exclusive.removeAll(common);
    }

    static String findAndPopNearestMatch(String l, List<String> right) {
        String current = null;
        // Ignore whitespace:
        l = l.replaceAll("\\s", "");
        int min = Integer.MAX_VALUE;
        for (String r : right) {
            int d = Levensthein.calculate(l, r.replaceAll("\\s", ""));
            if (d <= min) {
                current = r;
                min = d;
            }
        }
        right.remove(current);
        return current;
    }

    static List<Matching> findPairs(List<String> left, List<String> right) {
        List<Matching> pairs = new ArrayList<>(left.size() + right.size());
        int initCap =
            Math.max(8, Math.max(left.size() * right.size(), Math.max(left.size(), right.size())));
        PriorityQueue<Triple<Integer, Integer, Integer>> queue =
            new PriorityQueue<>(initCap, Comparator.comparingInt((t) -> t.third));
        for (int i = 0; i < left.size(); i++) {
            for (int j = 0; j < right.size(); j++) {
                queue.add(new Triple<>(i, j, Levensthein.calculate(left.get(i), right.get(j))));
            }
        }

        boolean[] matchedLeft = new boolean[left.size()];
        boolean[] matchedRight = new boolean[right.size()];
        while (!queue.isEmpty()) {
            Triple<Integer, Integer, Integer> t = queue.poll();
            /*
             * if(t.third>=THRESHOLD) { break; }
             */
            if (!matchedLeft[t.first] && !matchedRight[t.second]) {
                String l = left.get(t.first);
                String r = right.get(t.second);
                pairs.add(new Matching(l, r, t.third));
                matchedLeft[t.first] = true;
                matchedRight[t.second] = true;
            }
        }

        for (int i = 0; i < matchedLeft.length; i++) {
            if (!matchedLeft[i]) {
                pairs.add(new Matching(left.get(i), null, left.get(i).length()));
            }
        }
        for (int i = 0; i < matchedRight.length; i++) {
            if (!matchedRight[i]) {
                pairs.add(new Matching(null, right.get(i), right.get(i).length()));
            }
        }

        return pairs;
    }

    public void computeDiff() {
        computeDiff(leftAntec, rightAntec, commonAntec, exclusiveAntec);
        computeDiff(leftSucc, rightSucc, commonSucc, exclusiveSucc);
    }

    public List<String> getLeftAntec() {
        return leftAntec;
    }

    public List<String> getRightAntec() {
        return rightAntec;
    }

    public List<String> getRightSucc() {
        return rightSucc;
    }

    public List<String> getLeftSucc() {
        return leftSucc;
    }

    public Set<String> getExclusiveAntec() {
        return exclusiveAntec;
    }

    public Set<String> getCommonSucc() {
        return commonSucc;
    }

    public Set<String> getExclusiveSucc() {
        return exclusiveSucc;
    }

    public Set<String> getCommonAntec() {
        return commonAntec;
    }

    public List<Matching> getSuccPairs() {
        return findPairs(getLeftSucc(), getRightSucc());
    }

    public List<Matching> getAntecPairs() {
        return findPairs(getLeftAntec(), getRightAntec());
    }

    /**
     * https://www.baeldung.com/java-levenshtein-distance
     */
    static class Levensthein {
        static int calculate(String x, String y) {
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
                            dp[i - 1][j] + 1, dp[i][j - 1] + 1);
                    }
                }
            }
            return dp[x.length()][y.length()];
        }

        public static int costOfSubstitution(char a, char b) {
            return a == b ? 0 : 1;
        }


        public static int min(int... numbers) {
            return Arrays.stream(numbers).min().orElse(Integer.MAX_VALUE);
        }
    }

    static class Matching {
        final String left, right;
        final int distance;

        Matching(String left, String right, int distance) {
            this.left = left;
            this.right = right;
            this.distance = distance;
        }

        public String getLeft() {
            return left;
        }

        public String getRight() {
            return right;
        }

        public int getDistance() {
            return distance;
        }

        @Override
        public String toString() {
            return String.format("(%s, %s)", left, right);
        }
    }
}
