/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.*;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.AssertionFailure;

import org.key_project.util.LRUCache;

/**
 * Establishes a cache for the applied rule apps to query them by name.
 * See the get method for additional required constraints for correctness.
 *
 * @author Julian Wiesler
 */
public class AppliedRuleAppsNameCache {
    /** cache of all applied rules by name of a node */
    private final LRUCache<Node, HashMap<Name, List<RuleApp>>> cache = new LRUCache<>(32);

    private final ReentrantReadWriteLock lock = new ReentrantReadWriteLock();
    private final ReentrantReadWriteLock.ReadLock readLock = lock.readLock();
    private final ReentrantReadWriteLock.WriteLock writeLock = lock.writeLock();

    public AppliedRuleAppsNameCache() {}

    /**
     * Fills the cache value of this instance for node
     *
     * @param node the node
     * @return the value
     */
    private @Nonnull HashMap<Name, List<RuleApp>> fillCacheForNode(Node node) {
        HashMap<Name, List<RuleApp>> nodeCache;
        try {
            writeLock.lock();
            nodeCache = cache.get(node);
            if (nodeCache == null) {
                // Try to use parent cache to initialize the new cache
                HashMap<Name, List<RuleApp>> parentCache =
                    node.root() ? null : cache.get(node.parent());
                nodeCache = new HashMap<>();

                if (parentCache != null) {
                    if (node.parent().childrenCount() <= 1) {
                        // Parent cache will be removed, reuse it
                        nodeCache = parentCache;
                    } else {
                        // Copy the parent cache
                        for (Map.Entry<Name, List<RuleApp>> entry : parentCache.entrySet()) {
                            nodeCache.put(entry.getKey(), new ArrayList<>(entry.getValue()));
                        }
                    }

                    // Parent did not have a rule applied when we calculated this, add the rule
                    // applied
                    // there
                    RuleApp parentApp = node.parent().getAppliedRuleApp();
                    nodeCache.computeIfAbsent(parentApp.rule().name(), k -> new ArrayList<>())
                            .add(parentApp);

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

                        RuleApp a = par.getAppliedRuleApp();
                        nodeCache.computeIfAbsent(a.rule().name(), k -> new ArrayList<>()).add(a);

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
     * Gets rule apps applied to any node before the given node with the given name.
     *
     * Multiple assumptions about nodes:
     * * The given node is a leaf, no children, no applied rule
     * * Only *new* nodes are appended to nodes
     * * Non leaf nodes are not changed, pruning is allowed
     * * If the tree is pruned the removed nodes are discarded and not reused
     *
     * @param node the node
     * @param name the name
     * @return rule apps
     */
    public @Nonnull List<RuleApp> get(@Nonnull Node node, @Nonnull Name name) {
        if (node.getAppliedRuleApp() != null || node.childrenCount() != 0) {
            throw new AssertionFailure("Expected an empty leaf node");
        }

        HashMap<Name, List<RuleApp>> nodeCache;
        try {
            readLock.lock();
            nodeCache = cache.get(node);
        } finally {
            readLock.unlock();
        }

        if (nodeCache == null) {
            nodeCache = fillCacheForNode(node);
        }

        List<RuleApp> apps = nodeCache.get(name);
        return apps == null ? Collections.emptyList() : Collections.unmodifiableList(apps);
    }
}
