package de.uka.ilkd.key.gui.utilities;

import java.awt.Dimension;

import javax.swing.Action;
import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JTabbedPane;
import javax.swing.UIManager;

import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * Tab component for {@link JTabbedPane} with a close button.
 *
 * @author lanzinger
 */
public class ClosableTabComponent extends JPanel {

    private static final long serialVersionUID = -7205139488676599833L;

    /**
     * Creates a new {@code ClosableTabComponent}.
     *
     * @param title the component's title.
     * @param closeAction the action to execute when the component is closed.
     */
    public ClosableTabComponent(String title, Action closeAction) {
        setOpaque(false);

        JLabel label = new JLabel(title);
        label.setBackground(UIManager.getColor("TabbedPane.background"));
        add(label);

        JButton button = new JButton(IconFactory.quit(16));
        button.setContentAreaFilled(false);
        button.setPreferredSize(new Dimension(16, 16));
        button.addActionListener(closeAction::actionPerformed);
        add(button);
    }
}
