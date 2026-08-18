/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ProofSettings;

/**
 * for debugging - opens a window with the settings from current Proof and the default settings
 */
public class ShowActiveSettingsAction extends MainWindowAction {
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
        ProofSettings settings =
            (getMediator().getSelectedProof() == null) ? null
                    : getMediator().getSelectedProof().getSettings();
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
        dialog.optionTree.setSelectionPath(new TreePath(item.getPath()));
    }

    /**
     * The old (cleaned up) SettingsDialog.
     */
    private class ViewSettingsDialog extends JDialog {
        private final JTree optionTree = new JTree();

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

            optionTree.getParent().setMinimumSize(optionTree.getPreferredSize());
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
