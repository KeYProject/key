package de.uka.ilkd.key.gui;

import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
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

    private static Map<Name, Map<Integer, SortedSet<NodeInfoWindow>>> instances = new HashMap<>();

    /**
     * Returns {@code true} iff there are any open {@code NodeInfoWindow}s
     * associated with the specified node.
     *
     * @param node a node.
     * @return {@code true} iff there are any open {@code NodeInfoWindow}s
     *  associated with the specified node.
     */
    public static boolean hasInstances(Node node) {
        return instances
                .getOrDefault(node.proof().name(), Collections.emptyMap())
                .containsKey(node.serialNr());
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
     * Ensures that the specified window will not be returned by {@link #getInstances(Node)}.
     *
     * @param win the window to unregister.
     * @see #getInstances(Node)
     */
    protected static void unregister(NodeInfoWindow win) {
        Node node = win.getNode();
        instances.get(node.proof().name()).get(node.serialNr()).remove(win);
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

        win.addWindowListener(new WindowAdapter() {

           @Override
            public void windowClosed(WindowEvent event) {
               unregister(win);
            }
        });
    }

    private Node node;
    private String name;

    /**
     * Creates a new {@link NodeInfoWindow}.
     *
     * @param node the node this window is associated with.
     * @param name the window's name.
     */
    public NodeInfoWindow(Node node, String name) {
        this.node = node;
        this.name = name;
        setTitle(name);

        register(this);
    }

    @Override
    public int compareTo(NodeInfoWindow other) {
        return name.compareTo(other.name);
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
        return name;
    }
}
