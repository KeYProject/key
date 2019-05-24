package de.uka.ilkd.key.gui;

import javax.swing.JFrame;

import de.uka.ilkd.key.gui.ext.KeYGuiExtensionFacade;
import de.uka.ilkd.key.proof.Node;

public abstract class AdditionalWindow extends JFrame {

    private Node node;
    private String name;

    public AdditionalWindow(Node node, String name) {
        this.node = node;
        this.name = name;
        KeYGuiExtensionFacade.getPanel(OpenWindowsList.class).get().register(this);
    }

    public final Node getNode() {
        return node;
    }

    @Override
    public final String toString() {
        return name;
    }
}
