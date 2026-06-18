/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.prover.rules.RuleApp;

/**
 * Deterministic, prover-agnostic summary of a finished {@link Proof}.
 *
 * <p>
 * This is the measurement primitive for the multithreading equivalence gate: run the same proof
 * obligation under two prover configurations (e.g. single-threaded vs. one-thread-per-goal) and
 * assert their fingerprints match. If they differ, the parallel run produced a different proof and
 * is therefore not yet trustworthy.
 *
 * <p>
 * Two structural digests are recorded:
 * <ul>
 * <li>{@link #orderedDigest} hashes the proof tree in child-insertion order. It is the strictest
 * check and is appropriate whenever scheduling is deterministic (e.g. two single-threaded runs).
 * <li>{@link #canonicalDigest} hashes each node together with its children sorted by their own
 * subtree digest. It is invariant under sibling reordering, so it stays stable even when a parallel
 * scheduler inserts independent branches in a different order. The parallel gate compares this one.
 * </ul>
 *
 * @author Claude (KeY multithreading effort)
 */
public final class ProofFingerprint {

    /** Marker emitted for a closed leaf that has no applied rule of its own. */
    private static final String CLOSED_LEAF = "<closed>";
    /** Marker emitted for an open leaf (a remaining goal). */
    private static final String OPEN_LEAF = "<open>";

    /** Whether the whole proof is closed. */
    public final boolean closed;
    /** Number of open goals remaining. */
    public final int openGoals;
    /** Number of closed goals. */
    public final int closedGoals;
    /** Total number of nodes in the proof tree. */
    public final int nodeCount;
    /** Number of branches in the proof tree. */
    public final int branchCount;
    /** Digest of the tree walked in child-insertion order (scheduling-sensitive). */
    public final String orderedDigest;
    /** Digest of the tree with siblings canonically ordered (scheduling-insensitive). */
    public final String canonicalDigest;

    private ProofFingerprint(boolean closed, int openGoals, int closedGoals, int nodeCount,
            int branchCount, String orderedDigest, String canonicalDigest) {
        this.closed = closed;
        this.openGoals = openGoals;
        this.closedGoals = closedGoals;
        this.nodeCount = nodeCount;
        this.branchCount = branchCount;
        this.orderedDigest = orderedDigest;
        this.canonicalDigest = canonicalDigest;
    }

    /**
     * Computes the fingerprint of a (typically finished) proof.
     *
     * @param proof the proof to summarize; must not be {@code null}
     * @return its fingerprint
     */
    public static ProofFingerprint of(Proof proof) {
        Objects.requireNonNull(proof, "proof");
        StringBuilder ordered = new StringBuilder();
        String canonical = digest(proof.root(), false, ordered);
        return new ProofFingerprint(proof.closed(), proof.openGoals().size(),
            proof.closedGoals().size(), proof.countNodes(), proof.countBranches(),
            sha256(ordered.toString()), canonical);
    }

    /**
     * Recursively builds the subtree digest of {@code node}.
     *
     * @param node the subtree root
     * @param canonicalOrder unused flag kept for symmetry; ordering is handled per-call below
     * @param orderedOut accumulates the insertion-order traversal as a side effect
     * @return the canonical (sibling-order-independent) digest of this subtree
     */
    private static String digest(Node node, boolean canonicalOrder, StringBuilder orderedOut) {
        String label = labelOf(node);
        orderedOut.append(label).append('(');

        int n = node.childrenCount();
        List<String> childDigests = new ArrayList<>(n);
        for (int i = 0; i < n; i++) {
            childDigests.add(digest(node.child(i), canonicalOrder, orderedOut));
        }
        orderedOut.append(')');

        // Canonical digest: order children by their own subtree digest so that two proofs that
        // differ only in the order independent branches were explored hash identically.
        childDigests.sort(null);
        StringBuilder canonical = new StringBuilder(label).append('(');
        for (String cd : childDigests) {
            canonical.append(cd).append(',');
        }
        canonical.append(')');
        return sha256(canonical.toString());
    }

    /** The stable label of a node: its applied rule name, or a leaf marker. */
    private static String labelOf(Node node) {
        RuleApp app = node.getAppliedRuleApp();
        if (app != null) {
            return app.rule().name().toString();
        }
        return node.isClosed() ? CLOSED_LEAF : OPEN_LEAF;
    }

    private static String sha256(String s) {
        try {
            MessageDigest md = MessageDigest.getInstance("SHA-256");
            byte[] hash = md.digest(s.getBytes(StandardCharsets.UTF_8));
            StringBuilder sb = new StringBuilder(hash.length * 2);
            for (byte b : hash) {
                sb.append(Character.forDigit((b >> 4) & 0xF, 16));
                sb.append(Character.forDigit(b & 0xF, 16));
            }
            return sb.toString();
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 unavailable", e);
        }
    }

    /**
     * Strict equality: every field including the scheduling-sensitive {@link #orderedDigest}.
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof ProofFingerprint other)) {
            return false;
        }
        return closed == other.closed && openGoals == other.openGoals
                && closedGoals == other.closedGoals && nodeCount == other.nodeCount
                && branchCount == other.branchCount && orderedDigest.equals(other.orderedDigest)
                && canonicalDigest.equals(other.canonicalDigest);
    }

    @Override
    public int hashCode() {
        return Objects.hash(closed, openGoals, closedGoals, nodeCount, branchCount, orderedDigest,
            canonicalDigest);
    }

    /**
     * Equivalence up to sibling ordering: the two proofs reach the same result with the same tree
     * shape, but independent branches may have been explored in a different order. This is the
     * relation the parallel-vs-single gate asserts.
     *
     * @param other the fingerprint to compare against
     * @return {@code true} if the proofs are equivalent modulo branch order
     */
    public boolean equalsModuloOrder(ProofFingerprint other) {
        if (other == null) {
            return false;
        }
        return closed == other.closed && openGoals == other.openGoals
                && closedGoals == other.closedGoals && nodeCount == other.nodeCount
                && branchCount == other.branchCount
                && canonicalDigest.equals(other.canonicalDigest);
    }

    @Override
    public String toString() {
        return "ProofFingerprint{closed=" + closed + ", open=" + openGoals + ", closed="
            + closedGoals + ", nodes=" + nodeCount + ", branches=" + branchCount + ", ordered="
            + orderedDigest.substring(0, 12) + ", canonical=" + canonicalDigest.substring(0, 12)
            + '}';
    }
}
