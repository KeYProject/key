/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.*;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.AssertionFailure;

import org.key_project.logic.Name;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.ConcurrentLruCache;

import org.jspecify.annotations.NonNull;


/**
 * Establishes a cache for the applied rule apps to query them by name.
 * See the get method for additional required constraints for correctness.
 * <p>
 * Within a rule name the applied apps are additionally bucketed by an application
 * <em>fingerprint</em> ({@link #focusFingerprint}: the operators of the focus term and its direct
 * subterms), or {@code 0} for find-less apps. This turns the duplicate search in
 * {@link AbstractNonDuplicateAppFeature} from a linear scan over all same-named applications on the
 * branch into a bucket lookup. It is sound for every duplicate check because each one's
 * {@code comparePio} implies the two focus terms are equal up to term labels:
 * {@link NonDuplicateAppFeature} (equal positions), {@link EqNonDuplicateAppFeature} (equal
 * positions modulo formula renaming) and {@link NonDuplicateAppModPositionFeature} (equal focus
 * terms modulo irrelevant labels). The fingerprint is built only from operators (never from term
 * labels), so focus terms that are equal up to labels always share a fingerprint, and a duplicate
 * can only ever live in the candidate's own bucket -- including for the modulo-position variant,
 * which deliberately matches the same focus term at different sequent positions.
 *
 * @author Julian Wiesler
 */
public class AppliedRuleAppsNameCache {
    /** cache of all applied rules of a node, by rule name and then by application fingerprint */
    private final ConcurrentLruCache<Node, HashMap<Name, HashMap<Integer, List<RuleApp>>>> cache =
        new ConcurrentLruCache<>(32);

    private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
    private final ReentrantReadWriteLock.ReadLock readLock = lock.readLock();
    private final ReentrantReadWriteLock.WriteLock writeLock = lock.writeLock();

    public AppliedRuleAppsNameCache() {}

    /**
     * A cheap, label-insensitive fingerprint of a focus term for bucketing applied rule apps: the
     * top operator plus the operators of its direct subterms. It is built only from operators (an
     * operator is not a term label), so it is invariant under the mod-term-labels equality the
     * buckets are probed with -- a duplicate therefore always shares the candidate's bucket. It is
     * O(arity) and touches no subterm below depth one, unlike a full term hash. Coarser than a full
     * hash (more terms may share a bucket), but the {@code sameApplication} scan resolves any
     * collision, so this only trades a little bucket length for a much cheaper fingerprint.
     */
    public static int focusFingerprint(org.key_project.logic.Term focus) {
        int h = focus.op().hashCode();
        final int arity = focus.arity();
        h = 31 * h + arity;
        for (int i = 0; i < arity; i++) {
            h = 31 * h + focus.sub(i).op().hashCode();
        }
        return h;
    }

    /**
     * @return the fingerprint of a rule application ({@link #focusFingerprint} of its focus term),
     *         or {@code 0} for a find-less application. A find-less app uses {@code 0}; should a
     *         focus term also fingerprint to {@code 0} the only effect is a shared bucket, which
     *         the {@code sameApplication} scan resolves.
     */
    private static int fingerprint(RuleApp app) {
        final PosInOccurrence pio = app.posInOccurrence();
        return pio == null ? 0 : focusFingerprint(pio.subTerm());
    }

    private static void add(HashMap<Name, HashMap<Integer, List<RuleApp>>> nodeCache, RuleApp app) {
        nodeCache.computeIfAbsent(app.rule().name(), k -> new HashMap<>())
                .computeIfAbsent(fingerprint(app), k -> new ArrayList<>())
                .add(app);
    }

    /**
     * Fills the cache value of this instance for node
     *
     * @param node the node
     * @return the value
     */
    private @NonNull HashMap<Name, HashMap<Integer, List<RuleApp>>> fillCacheForNode(
            Node node) {
        HashMap<Name, HashMap<Integer, List<RuleApp>>> nodeCache;
        try {
            writeLock.lock();
            nodeCache = cache.get(node);
            if (nodeCache == null) {
                // Try to use parent cache to initialize the new cache
                HashMap<Name, HashMap<Integer, List<RuleApp>>> parentCache =
                    node.root() ? null : cache.get(node.parent());
                nodeCache = new HashMap<>();

                if (parentCache != null) {
                    if (node.parent().childrenCount() <= 1) {
                        // Parent cache will be removed, reuse it
                        nodeCache = parentCache;
                    } else {
                        // Copy the parent cache
                        for (Map.Entry<Name, HashMap<Integer, List<RuleApp>>> entry : parentCache
                                .entrySet()) {
                            HashMap<Integer, List<RuleApp>> buckets = new HashMap<>();
                            for (Map.Entry<Integer, List<RuleApp>> bucket : entry.getValue()
                                    .entrySet()) {
                                buckets.put(bucket.getKey(), new ArrayList<>(bucket.getValue()));
                            }
                            nodeCache.put(entry.getKey(), buckets);
                        }
                    }

                    // Parent did not have a rule applied when we calculated this, add the rule
                    // applied
                    // there
                    add(nodeCache, node.parent().getAppliedRuleApp());

                    // If this is an inner node, we hope we will never revisit it, remove it from
                    // the
                    // cache
                    if (node.parent().childrenCount() <= 1) {
                        cache.remove(node.parent());
                    }
                } else {
                    // Check all earlier rule applications
                    Node current = node;
                    while (!current.root()) {
                        final Node par = current.parent();
                        add(nodeCache, par.getAppliedRuleApp());
                        current = par;
                    }
                }

                cache.put(node, nodeCache);
            }
        } finally {
            writeLock.unlock();
        }

        return nodeCache;
    }

    /**
     * Gets rule apps applied to any node before the given node with the given name and the given
     * application fingerprint (see {@link #fingerprint(RuleApp)}).
     * <p>
     * Multiple assumptions about nodes:
     * * The given node is a leaf, no children, no applied rule
     * * Only *new* nodes are appended to nodes
     * * Non leaf nodes are not changed, pruning is allowed
     * * If the tree is pruned the removed nodes are discarded and not reused
     *
     * @param node the node
     * @param name the name
     * @param fingerprint the application fingerprint to restrict to
     * @return rule apps
     */
    public @NonNull List<RuleApp> get(@NonNull Node node,
            @NonNull Name name, int fingerprint) {
        if (node.getAppliedRuleApp() != null || node.childrenCount() != 0) {
            throw new AssertionFailure("Expected an empty leaf node");
        }

        HashMap<Name, HashMap<Integer, List<RuleApp>>> nodeCache;
        try {
            readLock.lock();
            nodeCache = cache.get(node);
        } finally {
            readLock.unlock();
        }

        if (nodeCache == null) {
            nodeCache = fillCacheForNode(node);
        }

        HashMap<Integer, List<RuleApp>> byFingerprint = nodeCache.get(name);
        if (byFingerprint == null) {
            return Collections.emptyList();
        }
        List<RuleApp> apps = byFingerprint.get(fingerprint);
        return apps == null ? Collections.emptyList() : Collections.unmodifiableList(apps);
    }
}
