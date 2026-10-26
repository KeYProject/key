/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import javax.swing.JComponent;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * <p>
 * A UI component showing additional information about a {@link Node} in the current {@link Proof}.
 * </p>
 *
 * @author lanzinger
 */
@NullMarked
public abstract class NodeInfoVisualizer extends JComponent
        implements Comparable<NodeInfoVisualizer> {
    private static final long serialVersionUID = 4205276651552216532L;

    /** @see #getInstances(Node) */
    private static final Map<Name, Map<Integer, SortedSet<NodeInfoVisualizer>>> instances =
        new HashMap<>();

    /**
     * @see #addListener(NodeInfoVisualizerListener)
     * @see #removeListener(NodeInfoVisualizerListener)
     */
    private static final Set<NodeInfoVisualizerListener> listeners = new HashSet<>();

    /** @see #getNode() */
    private @Nullable Node node;

    /** @see #getLongName() */
    private final String longName;

    /** @see #getShortName() */
    private final String shortName;

    /**
     * Creates a new {@link NodeInfoVisualizer}.
     *
     * @param node the node this visualizer is associated with.
     * @param longName the visualizer's long name.
     * @param shortName the visualizer's short name.
     *
     *        <p>
     *        The visualizer is registered while the receiver is still under initialization (EISOP
     *        initialization check); registration only stores the reference, everything else
     *        happens after construction, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    protected NodeInfoVisualizer(Node node, String longName, String shortName) {
        this.node = node;
        this.longName = longName;
        this.shortName = shortName;

        register(this);
    }

    /**
     * Returns {@code true} iff there are any open {@code NodeInfoWindow}s associated with the
     * specified node.
     *
     * @param node a node.
     * @return {@code true} iff there are any open {@code NodeInfoWindow}s associated with the
     *         specified node.
     */
    public static boolean hasInstances(Node node) {
        return !getInstances(node).isEmpty();
    }

    /**
     * Returns the set of open {@code NodeInfoWindow}s associated with the specified node.
     *
     * @param node a node.
     * @return the set of open {@code NodeInfoWindow}s associated with the specified node.
     */
    public static SortedSet<NodeInfoVisualizer> getInstances(Node node) {
        return Collections.unmodifiableSortedSet(
            instances.getOrDefault(node.proof().name(), Collections.emptyMap())
                    .getOrDefault(node.serialNr(), Collections.emptySortedSet()));
    }

    /**
     * Adds a listener.
     *
     * @param listener the listener to add.
     */
    public static void addListener(NodeInfoVisualizerListener listener) {
        listeners.add(listener);
    }

    /**
     * Removes a listener.
     *
     * @param listener the listener to remove.
     */
    public static void removeListener(NodeInfoVisualizerListener listener) {
        listeners.remove(listener);
    }

    /**
     * Ensures that the specified visualizer will not be returned by {@link #getInstances(Node)}.
     *
     * @param vis the visualizer to unregister.
     * @see #getInstances(Node)
     */
    protected static void unregister(NodeInfoVisualizer vis) {
        Node node = vis.getNode();
        if (node == null) {
            // the node is only cleared by dispose(), which unregisters first
            return;
        }
        Map<Integer, SortedSet<NodeInfoVisualizer>> proofMap = instances.get(node.proof().name());
        if (proofMap == null) {
            return;
        }
        SortedSet<NodeInfoVisualizer> nodeSet = proofMap.get(node.serialNr());
        if (nodeSet != null && nodeSet.remove(vis)) {
            synchronized (listeners) {
                for (NodeInfoVisualizerListener listener : listeners) {
                    listener.visualizerUnregistered(vis);
                }
            }
        }
    }

    private static void register(NodeInfoVisualizer vis) {
        Node node = vis.getNode();
        if (node == null) {
            // a visualizer is registered before its node is ever cleared
            throw new NullPointerException("No node available.");
        }
        int nodeNr = node.serialNr();
        Proof proof = node.proof();
        Name proofName = proof.name();

        instances.putIfAbsent(proofName, new TreeMap<>());

        Map<Integer, SortedSet<NodeInfoVisualizer>> map = instances.get(proofName);
        if (map == null) {
            // the entry has just been put into the map
            throw new NullPointerException("No proof map available.");
        }
        map.putIfAbsent(nodeNr, new TreeSet<>());
        SortedSet<NodeInfoVisualizer> nodeSet = map.get(nodeNr);
        if (nodeSet == null) {
            // the entry has just been put into the map
            throw new NullPointerException("No node set available.");
        }
        nodeSet.add(vis);

        synchronized (listeners) {
            for (NodeInfoVisualizerListener listener : listeners) {
                listener.visualizerRegistered(vis);
            }
        }
    }

    /**
     * Frees any resources belonging to this visualizer and removes it from
     * {@link #getInstances(Node)}.
     */
    public void dispose() {
        unregister(this);
        node = null;
    }

    @Override
    public int compareTo(NodeInfoVisualizer other) {
        return longName.compareTo(other.longName);
    }

    /**
     *
     * @return the node this window is associated with, or {@code null} once
     *         {@link #dispose()} has released the reference.
     */
    public final @Nullable Node getNode() {
        return node;
    }

    @Override
    public final String toString() {
        return longName;
    }

    @Override
    public String getName() {
        return shortName;
    }

    /**
     *
     * @return the window's long name
     * @see #getShortName()
     */
    public final String getLongName() {
        return longName;
    }

    /**
     *
     * @return the window's short name
     * @see #getLongName()
     */
    public final String getShortName() {
        return shortName;
    }
}
