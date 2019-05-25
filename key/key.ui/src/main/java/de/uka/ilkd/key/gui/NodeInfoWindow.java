package de.uka.ilkd.key.gui;

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.ext.KeYGuiExtensionFacade;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 *  A window showing additional information about a {@link Node} in the current {@link Proof}.
 * </p>
 *
 * <p>
 *  {@code NodeInfoWindow}s are automatically added to the {@link NodeInfoWindowsList}
 * </p>
 *
 * @author lanzinger
 */
public abstract class NodeInfoWindow extends JFrame {

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

        KeYGuiExtensionFacade.getPanel(NodeInfoWindowsList.class).get().register(this);
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
