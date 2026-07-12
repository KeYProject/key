/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

/**
 * Failure-message building blocks for the multi-core prover CI tests.
 * <p>
 * These tests exist to catch thread-safety and determinism mistakes in <em>other people's</em>
 * changes, often written by developers who have never worked with the multi-core prover. A bare
 * "expected true but was false" would leave them stranded, so every gate appends the matching
 * advice block: what kind of mistake typically produces this failure, and where the fix patterns
 * are documented ({@code key.core/src/main/java/de/uka/ilkd/key/prover/README.md}).
 */
public final class MtFailureAdvice {

    /** Pointer appended to every advice block. */
    private static final String README =
        "key.core/src/main/java/de/uka/ilkd/key/prover/README.md";

    private MtFailureAdvice() {
    }

    /**
     * Advice for a proof that behaves differently between two single-core runs.
     *
     * @return the advice text, starting with a newline
     */
    public static String scDeterminism() {
        return "\n\n--- What this failure means -------------------------------------------\n"
            + "The SAME problem was proved twice in this JVM with the single-core prover\n"
            + "and produced two DIFFERENT proof trees. Proof search must be reproducible;\n"
            + "if it is not, some part of rule selection depends on an accidental order.\n"
            + "Typical causes, most common first:\n"
            + "  1. Iterating a HashMap/HashSet (no guaranteed order) somewhere that feeds\n"
            + "     rule costs, candidate lists, or queue order. Use LinkedHashMap/-Set,\n"
            + "     ImmutableList, or sort before iterating.\n"
            + "  2. A cache whose stored value depends on WHEN it was stored, with an\n"
            + "     eviction order that differs between runs (see the cache table in\n"
            + "     " + README + ").\n"
            + "  3. Ordering by Object.hashCode()/identity hash, which changes per JVM run.\n"
            + "Reproduce locally: ./gradlew :key.core:testMt2w --tests '*ScDeterminism*'\n";
    }

    /**
     * Advice for a proof that fails (or degrades) under the multi-core prover but works
     * single-core.
     *
     * @return the advice text, starting with a newline
     */
    public static String mtCorpus() {
        return "\n\n--- What this failure means -------------------------------------------\n"
            + "This proof closes with the single-core prover but failed here under the\n"
            + "multi-core prover (several worker threads, each searching on its own open\n"
            + "goal). If your change touches rule, strategy, proof or logic code, the\n"
            + "typical causes are:\n"
            + "  1. A shared object that remembers something between calls: rules,\n"
            + "     strategy features and match instructions are singletons used by ALL\n"
            + "     workers at once -- a 'last call' field on one of them mixes up two\n"
            + "     goals. Move such memos into a ThreadLocal.\n"
            + "  2. A plain HashMap/HashSet/ArrayList used as a static cache -- two\n"
            + "     workers writing at the same time corrupt it. Pick a replacement from\n"
            + "     the cache table in " + README + ".\n"
            + "  3. Fresh names minted from a proof-global counter -- names then depend\n"
            + "     on which worker asks first. Derive names from the goal-local\n"
            + "     namespaces instead.\n"
            + "Reproduce locally: ./gradlew :key.core:testMt2w   (2 workers)\n"
            + "                   ./gradlew :key.core:testMt4w   (4 workers, splitting set)\n"
            + "A run-to-run flicker (passes when repeated) is still a real finding: races\n"
            + "are timing-dependent. Treat the first failure as the signal.\n";
    }
}
