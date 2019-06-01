package de.uka.ilkd.key.gui;

/**
 * A listener to the {@link NodeInfoWindow} class. Listeners are notified whenever a window is
 * registered or unregistered from {@link NodeInfoWindow#getInstances(de.uka.ilkd.key.proof.Node)}.
 *
 * @author lanzinger
 */
public interface NodeInfoWindowListener {

    void windowRegistered(NodeInfoWindow win);
    void windowUnregistered(NodeInfoWindow win);
}
