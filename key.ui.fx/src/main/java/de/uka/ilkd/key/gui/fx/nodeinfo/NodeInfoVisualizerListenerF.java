/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.nodeinfo;

/**
 * JavaFX port of the Swing {@code de.uka.ilkd.key.gui.NodeInfoVisualizerListener}: notified
 * whenever a {@link NodeInfoVisualizerF} is registered or unregistered from
 * {@link NodeInfoVisualizerF#getInstances(de.uka.ilkd.key.proof.Node)}.
 *
 * @author lanzinger (Swing original), the key.ui.fx team (port)
 */
public interface NodeInfoVisualizerListenerF {

    /**
     * Called when a new visualizer has been registered.
     *
     * @param vis the registered visualizer
     */
    void visualizerRegistered(NodeInfoVisualizerF vis);

    /**
     * Called when a visualizer has been unregistered.
     *
     * @param vis the unregistered visualizer
     */
    void visualizerUnregistered(NodeInfoVisualizerF vis);
}
