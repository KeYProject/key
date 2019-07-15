package de.uka.ilkd.key.gui;

/**
 * A listener to the {@link NodeInfoWindow} class. Listeners are notified whenever a window is
 * registered or unregistered from {@link NodeInfoWindow#getInstances(de.uka.ilkd.key.proof.Node)}.
 *
 * @author lanzinger
 */
public interface NodeInfoWindowListener {

    /**
     * Called when a new winder has been registered.
     *
     * @param win the registered window.
     */
    void windowRegistered(NodeInfoWindow win);

    /**
     * Called when a window has been unregistered.
     *
     * @param win the unregistered window.
     */
    void windowUnregistered(NodeInfoWindow win);
}
