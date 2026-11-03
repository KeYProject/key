/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.*;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeModel;
import javax.swing.tree.TreePath;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.gui.smt.OptionContentNode;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;

import org.jspecify.annotations.NullMarked;

/**
 * for debugging - opens a window with the settings from current Proof and the default settings
 */
@NullMarked
public class ShowActiveSettingsAction extends MainWindowAction {
    /**
     * The action-configuration setters are called on {@code this} while the receiver is still
     * under initialization (EISOP initialization check); safe here, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public ShowActiveSettingsAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Show All Active Settings");
        setIcon(IconFactory.properties(16));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        showDialog();
    }

    private ViewSettingsDialog showDialog() {
        Proof selectedProof = getMediator().getSelectedProof();
        // {@code settings} may be {@code null} when no proof is loaded; the tree model handles a
        // {@code null} proof settings object (see {@link SettingsTreeModel#generateTree()}).
        ProofSettings settings = selectedProof == null ? null : selectedProof.getSettings();
        SettingsTreeModel model =
            new SettingsTreeModel(settings, ProofIndependentSettings.DEFAULT_INSTANCE);
        ViewSettingsDialog dialog = new ViewSettingsDialog(model, model.getStartComponent());
        dialog.setTitle("All active settings");
        dialog.setLocationRelativeTo(mainWindow);
        dialog.setVisible(true);
        return dialog;
    }

    public void showAndFocusTacletOptions() {
        ViewSettingsDialog dialog = showDialog();
        SettingsTreeModel model = (SettingsTreeModel) dialog.optionTree.getModel();
        var item = model.getTacletOptionsItem();
        if (item == null) {
            throw new NullPointerException("Taclet options item is not part of the settings tree.");
        }
        dialog.optionTree.setSelectionPath(new TreePath(item.getPath()));
    }

    /**
     * The old (cleaned up) SettingsDialog.
     */
    private class ViewSettingsDialog extends JDialog {
        private final JTree optionTree = new JTree();

        /**
         * The {@code JDialog} configuration calls below operate on {@code this} while the receiver
         * is still under initialization (EISOP initialization check); safe here because the
         * dialog is only shown after construction completes ({@link #setVisible(boolean)} is
         * called by the caller), suppressed with a scoped key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        public ViewSettingsDialog(TreeModel model, JComponent startComponent) {
            super(mainWindow);

            optionTree.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));

            Container cp = this.getContentPane();
            cp.setLayout(new BorderLayout());
            cp.add(new JScrollPane(optionTree), BorderLayout.CENTER);

            JButton okButton = new JButton("OK");
            okButton.addActionListener(e -> dispose());
            setDefaultCloseOperation(DISPOSE_ON_CLOSE);
            JPanel buttons = new JPanel(new FlowLayout());
            buttons.add(okButton);
            cp.add(buttons, BorderLayout.SOUTH);

            final var selectedProof = mainWindow.getMediator().getSelectedProof();
            var name = selectedProof != null ? selectedProof.name() : "<b>no proof selected</b>";

            JLabel announce =
                new JLabel("<html>This shows the active settings for the proof: " + name + ".<br>" +
                    "To change settings for future proofs, use Options > Show Settings.");
            announce.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));
            cp.add(announce, BorderLayout.NORTH);
            optionTree.setModel(model);

            Container parent = optionTree.getParent();
            if (parent == null) {
                throw new NullPointerException("Option tree is not attached to a container.");
            }
            parent.setMinimumSize(optionTree.getPreferredSize());
            cp.setPreferredSize(computePreferredSize(model, optionTree));
            this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
            setIconImage(IconFactory.keyLogo());
            this.pack();
            this.setLocationRelativeTo(MainWindow.getInstance());

            getRootPane().registerKeyboardAction((e) -> dispose(),
                KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);
            getRootPane().setDefaultButton(okButton);
        }

        private static Dimension computePreferredSize(TreeModel model, JComponent comp) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode) model.getRoot();
            Dimension dim = computePreferredSize(node);
            dim.width = dim.width + comp.getPreferredSize().width + 100;
            dim.height = Math.min(dim.height, 400);
            return dim;
        }

        private static Dimension computePreferredSize(DefaultMutableTreeNode node) {

            Dimension dim = node instanceof OptionContentNode
                    ? new Dimension(((OptionContentNode) node).getComponent().getPreferredSize())
                    : new Dimension(0, 0);

            for (int i = 0; i < node.getChildCount(); i++) {
                Dimension dimChild =
                    computePreferredSize((DefaultMutableTreeNode) node.getChildAt(i));
                dim.width = Math.max(dimChild.width, dim.width);
                dim.height = Math.max(dimChild.height, dim.height);

            }
            return dim;
        }
    }
}
