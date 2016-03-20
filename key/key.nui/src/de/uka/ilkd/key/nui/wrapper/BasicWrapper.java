package de.uka.ilkd.key.nui.wrapper;

import javax.swing.JComponent;
import javax.swing.SwingUtilities;

import javafx.embed.swing.SwingNode;

/**
 * Basic Wrapper used to show Swing components in JavaFX.
 * 
 * @author Patrick Jattke
 *
 */
public abstract class BasicWrapper {

    /**
     * Creates a {@link SwingNode} from a given JComponent (Swing component).
     * The SwingNode can directly be added into the FX SceneGraph.
     * 
     * @param swingComponent
     *            The component desired to display in JavaFX.
     * @return SwingNode The FX Node containing the swingComponent.
     */
    protected SwingNode addSwingComponent(final JComponent swingComponent) {
        final SwingNode swingNode = new SwingNode();
        SwingUtilities.invokeLater(() -> swingNode.setContent(swingComponent));
        return swingNode;
    }
}
