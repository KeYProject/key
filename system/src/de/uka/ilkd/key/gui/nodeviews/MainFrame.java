package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.util.GuiUtilities;
import java.awt.Color;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.AbstractAction;
import javax.swing.JComponent;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.KeyStroke;
import javax.swing.border.EmptyBorder;

/**
 *
 * @author Kai Wallisch
 */
public class MainFrame extends JScrollPane {

    public static final Color openGoalRed = new Color(250, 90, 90);
    public static final Color openGoalRedLight =
            new Color((255 + 250) / 2, (90 + 250) / 2, (90 + 250) / 2);
    public static final Color transparent = new Color(0, 0, 0, 0);
    public SequentView sequentView;

    public void setSequentView(SequentView sequentView) {
        setViewportView(new MainFrameBody(sequentView));
    }

    public MainFrame() {

        setBorder(new EmptyBorder(0, 0, 0, 0));
        getVerticalScrollBar().setUnitIncrement(30);
        getHorizontalScrollBar().setUnitIncrement(30);

        // FIXME put this somewhere descent
        getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW).put(
                KeyStroke.getKeyStroke(KeyEvent.VK_C, Toolkit.getDefaultToolkit().getMenuShortcutKeyMask()),
                "copy");
        getActionMap().put("copy", new AbstractAction() {
            public void actionPerformed(ActionEvent e) {
                GuiUtilities.copyHighlightToClipboard(MainWindow.getInstance().leafNodeView);
            }
        });

        setSequentView(new EmptySequent());
    }

    private class MainFrameBody extends JPanel {

        public MainFrameBody(SequentView sequentView) {

            setLayout(new GridBagLayout());
            setBackground(SequentView.BACKGROUND_COLOR);

            GridBagConstraints gbc = new GridBagConstraints();

            gbc.fill = GridBagConstraints.HORIZONTAL;
            gbc.gridx = 1;
            gbc.gridy = 0;
            gbc.weightx = 1.0;
            gbc.weighty = 0.0;
            add( javax.swing.Box.createGlue(), gbc);

            Insets titleButtonInsets = new Insets(0, 50, 4, 0);
            gbc.insets = titleButtonInsets;
            gbc.fill = GridBagConstraints.NONE;
            gbc.gridx = 0;
            gbc.gridy = 0;
            gbc.weightx = 0.0;
            gbc.weighty = 0.0;
            add(sequentView.titleButton, gbc);

            gbc.insets = new Insets(0, 0, 0, 0);
            gbc.fill = GridBagConstraints.HORIZONTAL;
            gbc.gridx = 0;
            gbc.gridy = 1;
            gbc.weightx = 1.0;
            gbc.weighty = 0.0;
            gbc.gridwidth = 2;
            add(sequentView, gbc);

            if (sequentView instanceof InnerNodeView) {
                gbc.gridy = 2;
                add(((InnerNodeView) sequentView).tacletInfo, gbc);
            }
            
            gbc.fill = GridBagConstraints.BOTH;
            gbc.gridx = 0;
            gbc.gridy = 3;
            gbc.weighty = 1.0;
            add( javax.swing.Box.createGlue(), gbc);

            setBorder(new SequentBorder(sequentView.titleButton, titleButtonInsets));

        }
    }
}
