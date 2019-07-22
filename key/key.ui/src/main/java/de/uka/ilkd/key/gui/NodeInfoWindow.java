package de.uka.ilkd.key.gui;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;

import javax.swing.JFrame;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 *  A window showing additional information about a {@link Node} in the current {@link Proof}.
 * </p>
 *
 * @author lanzinger
 */
public abstract class NodeInfoWindow extends JFrame implements Comparable<NodeInfoWindow> {
    private static final long serialVersionUID = 4205276651552216532L;

    /** @see #getInstances(Node) */
    private static Map<Name, Map<Integer, SortedSet<NodeInfoWindow>>> instances = new HashMap<>();

    /**
     * @see #addListener(NodeInfoWindowListener)
     * @see #removeListener(NodeInfoWindowListener)
     */
    private static Set<NodeInfoWindowListener> listeners = new HashSet<>();

    /** @see #getNode() */
    private Node node;

    /** @see #getLongName() */
    private String longName;

    /** @see #getShortName() */
    private String shortName;

    /**
     * Creates a new {@link NodeInfoWindow}.
     *
     * @param node the node this window is associated with.
     * @param longName the window's long name.
     * @param shortName the window's short name.
     */
    public NodeInfoWindow(Node node, String longName, String shortName) {
        this.node = node;
        this.longName = longName;
        this.shortName = shortName;

        setTitle(shortName);

        register(this);
    }

    /**
     * Returns {@code true} iff there are any open {@code NodeInfoWindow}s
     * associated with the specified node.
     *
     * @param node a node.
     * @return {@code true} iff there are any open {@code NodeInfoWindow}s
     *  associated with the specified node.
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
    public static SortedSet<NodeInfoWindow> getInstances(Node node) {
        return Collections.unmodifiableSortedSet(instances
                .getOrDefault(node.proof().name(), Collections.emptyMap())
                .getOrDefault(node.serialNr(), Collections.emptySortedSet()));
    }

    /**
     * Adds a listener.
     *
     * @param listener the listener to add.
     */
    public static void addListener(NodeInfoWindowListener listener) {
        listeners.add(listener);
    }

    /**
     * Removes a listener.
     *
     * @param listener the listener to remove.
     */
    public static void removeListener(NodeInfoWindowListener listener) {
        listeners.remove(listener);
    }

    /**
     * Ensures that the specified window will not be returned by {@link #getInstances(Node)}.
     *
     * @param win the window to unregister.
     * @see #getInstances(Node)
     */
    protected static void unregister(NodeInfoWindow win) {
        Node node = win.getNode();
        if (instances.get(node.proof().name()).get(node.serialNr()).remove(win)) {
            synchronized (listeners) {
                for (NodeInfoWindowListener listener : listeners) {
                    listener.windowUnregistered(win);
                }
            }
        }
    }

    private static void register(NodeInfoWindow win) {
        Node node = win.getNode();
        int nodeNr = node.serialNr();
        Proof proof = node.proof();
        Name proofName = proof.name();

        instances.putIfAbsent(proofName, new TreeMap<>());

        Map<Integer, SortedSet<NodeInfoWindow>> map = instances.get(proofName);
        map.putIfAbsent(nodeNr, new TreeSet<>());
        map.get(nodeNr).add(win);

        synchronized (listeners) {
            for (NodeInfoWindowListener listener : listeners) {
                listener.windowRegistered(win);
            }
        }
    }

    @Override
    public void dispose() {
        unregister(this);
        node = null;
        super.dispose();
    }

    @Override
    public int compareTo(NodeInfoWindow other) {
        return longName.compareTo(other.longName);
    }

    /**
     *
     * @return the node this window is associated with.
     */
    public final Node getNode() {
        return node;
    }

    @Override
    public final String toString() {
        return longName;
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
