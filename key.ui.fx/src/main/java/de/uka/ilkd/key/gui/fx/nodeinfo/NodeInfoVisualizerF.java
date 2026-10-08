/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeinfo;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import javafx.stage.Stage;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;

/**
 * JavaFX port of the Swing {@code de.uka.ilkd.key.gui.NodeInfoVisualizer}: a UI component
 * (window) showing additional information about a {@link Node} in the current {@link Proof}.
 * <p>
 * The port keeps the Swing original's static registry semantics one to one
 * ({@code de.uka.ilkd.key.gui.NodeInfoVisualizer}): instances are collected per proof name and
 * node serial number ({@link #getInstances(Node)}, {@link #hasInstances(Node)}); listeners
 * ({@link NodeInfoVisualizerListenerF}) are notified whenever a visualizer is registered or
 * unregistered. The Swing base class is an abstract {@code JComponent} hosted by the source
 * view frame ({@code SourceViewFrame.addComponent}); the FX counterpart is an abstract
 * {@link Stage} — the Swing docking-based hosting has no FX equivalent yet, so a visualizer is
 * a free window owned by the main window (the same presentation as the ported
 * {@code ProofDiffFrameF}).
 * <p>
 * Subclasses must call {@link #dispose()} when they close (Swing {@code dispose()}), which
 * unregisters the instance and fires the listener.
 *
 * @author lanzinger (Swing original), the key.ui.fx team (port)
 */
public abstract class NodeInfoVisualizerF extends Stage implements Comparable<NodeInfoVisualizerF> {

    /** @see #getInstances(Node) */
    private static final Map<Name, Map<Integer, SortedSet<NodeInfoVisualizerF>>> instances =
        new HashMap<>();

    /** @see #addListener(NodeInfoVisualizerListenerF) */
    private static final Set<NodeInfoVisualizerListenerF> listeners = new HashSet<>();

    /** @see #getNode() */
    private Node node;

    /** @see #getLongName() */
    private final String longName;

    /** @see #getShortName() */
    private final String shortName;

    /**
     * Creates a new {@code NodeInfoVisualizerF} and registers it in the static instance registry.
     *
     * @param node the node this visualizer is associated with
     * @param longName the visualizer's long name
     * @param shortName the visualizer's short name
     */
    protected NodeInfoVisualizerF(Node node, String longName, String shortName) {
        this.node = node;
        this.longName = longName;
        this.shortName = shortName;
        register(this);
    }

    /**
     * @return {@code true} iff there are any open visualizers associated with the specified node
     *         (Swing {@code NodeInfoVisualizer.hasInstances})
     */
    public static boolean hasInstances(Node node) {
        return !getInstances(node).isEmpty();
    }

    /**
     * @return the set of open visualizers associated with the specified node (Swing
     *         {@code NodeInfoVisualizer.getInstances})
     */
    public static SortedSet<NodeInfoVisualizerF> getInstances(Node node) {
        return Collections.unmodifiableSortedSet(instances
                .getOrDefault(node.proof().name(), Collections.emptyMap())
                .getOrDefault(node.serialNr(), Collections.emptySortedSet()));
    }

    /**
     * Adds a listener (Swing {@code NodeInfoVisualizer.addListener}).
     *
     * @param listener the listener to add
     */
    public static void addListener(NodeInfoVisualizerListenerF listener) {
        listeners.add(listener);
    }

    /**
     * Removes a listener (Swing {@code NodeInfoVisualizer.removeListener}).
     *
     * @param listener the listener to remove
     */
    public static void removeListener(NodeInfoVisualizerListenerF listener) {
        listeners.remove(listener);
    }

    /**
     * Ensures that the specified visualizer will not be returned by {@link #getInstances(Node)}
     * (Swing {@code unregister}); fires {@code visualizerUnregistered} if it was registered.
     */
    protected static void unregister(NodeInfoVisualizerF vis) {
        Node node = vis.getNode();
        if (node == null) {
            return;
        }
        Map<Integer, SortedSet<NodeInfoVisualizerF>> map = instances.get(node.proof().name());
        boolean removed = map != null
                && map.getOrDefault(node.serialNr(), Collections.emptySortedSet()).remove(vis);
        if (removed) {
            synchronized (listeners) {
                for (NodeInfoVisualizerListenerF listener : listeners) {
                    listener.visualizerUnregistered(vis);
                }
            }
        }
    }

    private static void register(NodeInfoVisualizerF vis) {
        Node node = vis.getNode();
        int nodeNr = node.serialNr();
        Name proofName = node.proof().name();

        instances.putIfAbsent(proofName, new TreeMap<>());
        Map<Integer, SortedSet<NodeInfoVisualizerF>> map = instances.get(proofName);
        map.putIfAbsent(nodeNr, new TreeSet<>());
        map.get(nodeNr).add(vis);

        synchronized (listeners) {
            for (NodeInfoVisualizerListenerF listener : listeners) {
                listener.visualizerRegistered(vis);
            }
        }
    }

    /**
     * Frees any resources belonging to this visualizer, closes the window and removes it from
     * {@link #getInstances(Node)} (Swing {@code dispose()}).
     */
    public void dispose() {
        unregister(this);
        node = null;
        if (isShowing()) {
            hide();
        }
    }

    @Override
    public int compareTo(NodeInfoVisualizerF other) {
        return longName.compareTo(other.longName);
    }

    /**
     * @return the node this window is associated with (Swing {@code getNode()})
     */
    public final Node getNode() {
        return node;
    }

    /**
     * @return the window's long name (Swing {@code getLongName()})
     */
    public final String getLongName() {
        return longName;
    }

    /**
     * @return the window's short name (Swing {@code getShortName()})
     */
    public final String getShortName() {
        return shortName;
    }
}
