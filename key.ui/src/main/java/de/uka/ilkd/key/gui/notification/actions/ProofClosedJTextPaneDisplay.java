/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.notification.actions;

import java.awt.Dimension;
import java.awt.Font;
import java.awt.Frame;
import javax.swing.BorderFactory;
import javax.swing.JEditorPane;
import javax.swing.JOptionPane;
import javax.swing.JScrollPane;
import javax.swing.UIManager;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.ShowProofStatistics;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.notification.events.NotificationEvent;
import de.uka.ilkd.key.gui.notification.events.ProofClosedNotificationEvent;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Displays a JOptionPane informing about a closed proof and gives some statistics.
 *
 * @author bubel
 */
public class ProofClosedJTextPaneDisplay extends ShowDisplayPane {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofClosedJTextPaneDisplay.class);

    public ProofClosedJTextPaneDisplay(Frame parentComponent) {
        super(parentComponent);
    }

    /**
     * Displays a JOptionPane informing the user about a closed proof. If available some statistics
     * are displayed as well.
     */
    @Override
    public synchronized boolean execute(NotificationEvent pcne) {
        if (pcne instanceof ProofClosedNotificationEvent) {
            Proof proof = ((ProofClosedNotificationEvent) pcne).getProof();
            if (proof != null) {
                ShowProofStatistics.Window win =
                    new ShowProofStatistics.Window(MainWindow.getInstance(), proof);
                win.setVisible(true);
            }
        } else {
            setMessage("Proof Closed. No statistics available.");

            JEditorPane contentPane = new JEditorPane("text/html", getMessage());
            contentPane.setEditable(false);
            contentPane.setBorder(BorderFactory.createEmptyBorder());
            contentPane.setCaretPosition(0);
            contentPane.setBackground(MainWindow.getInstance().getBackground());
            contentPane.setSize(new Dimension(10, 360));
            contentPane.setPreferredSize(
                new Dimension(contentPane.getPreferredSize().width + 15, 360));

            JScrollPane scrollPane = new JScrollPane(contentPane);
            scrollPane.setBorder(BorderFactory.createEmptyBorder());

            Font myFont = UIManager.getFont(Config.KEY_FONT_PROOF_TREE);
            if (myFont != null) {
                contentPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
                contentPane.setFont(myFont);
            } else {
                LOGGER.debug("KEY_FONT_PROOF_TREE not available. Use standard font.");
            }

            JOptionPane.showMessageDialog(parentComponent, scrollPane, "Proof closed",
                JOptionPane.INFORMATION_MESSAGE);
        }

        return true;
    }
}
