package de.uka.ilkd.key.gui;

/**
 * A listener to the {@link NodeInfoVisualizer} class.
 * Listeners are notified whenever a visualizer is registered or unregistered from
 * {@link NodeInfoVisualizer#getInstances(de.uka.ilkd.key.proof.Node)}.
 *
 * @author lanzinger
 */
public interface NodeInfoVisualizerListener {

    /**
     * Called when a new visualizer has been registered.
     *
     * @param vis the registered visualizer.
     */
    void visualizerRegistered(NodeInfoVisualizer vis);

    /**
     * Called when a visualizer has been unregistered.
     *
     * @param vis the unregistered visualizer.
     */
    void visualizerUnregistered(NodeInfoVisualizer vis);
}
