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

    /**
     *
     */
    private static final long serialVersionUID = -3038735283059371442L;

    public ShowActiveSettingsAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Show All Active Settings");
        setIcon(IconFactory.properties(16));
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        ProofSettings settings =
            (getMediator().getSelectedProof() == null) ? ProofSettings.DEFAULT_SETTINGS
                    : getMediator().getSelectedProof().getSettings();
        SettingsTreeModel model =
            new SettingsTreeModel(settings, ProofIndependentSettings.DEFAULT_INSTANCE);
        ViewSettingsDialog dialog = new ViewSettingsDialog(model, model.getStartComponent());
        dialog.setTitle("All active settings");
        dialog.setLocationRelativeTo(mainWindow);
        dialog.setVisible(true);
    }

    /**
     * The old (cleaned up) SettingsDialog.
     */
    private class ViewSettingsDialog extends JDialog {
        private static final long serialVersionUID = -3780496399924182275L;
        private JTree optionTree;
        private JSplitPane splitPane;
        private JPanel optionPanel;

        public ViewSettingsDialog(TreeModel model, JComponent startComponent) {
            super(mainWindow);
            this.getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
            Box box = Box.createHorizontalBox();
            box.add(getSplitPane());
            this.getContentPane().add(box);
            this.getContentPane().add(Box.createVerticalStrut(5));
            box = Box.createHorizontalBox();
            box.add(Box.createHorizontalStrut(5));
            JButton okButton = new JButton("OK");
            okButton.addActionListener(e -> dispose());
            setDefaultCloseOperation(DISPOSE_ON_CLOSE);
            box.add(okButton);
            box.add(Box.createHorizontalStrut(5));
            this.getContentPane().add(box);
            this.getOptionTree().setModel(model);
            getSplitPane().setRightComponent(startComponent);

            this.getOptionTree().getParent().setMinimumSize(getOptionTree().getPreferredSize());
            this.getContentPane().setPreferredSize(computePreferredSize(model));
            this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
            setIconImage(IconFactory.keyLogo());
            this.pack();
            this.setLocationRelativeTo(MainWindow.getInstance());



            getRootPane().registerKeyboardAction((e) -> dispose(),
                KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);
            getRootPane().setDefaultButton(okButton);
        }

        private Dimension computePreferredSize(TreeModel model) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode) model.getRoot();
            Dimension dim = computePreferredSize(node);
            dim.width = dim.width + getOptionTree().getPreferredSize().width + 100;
            dim.height = Math.min(dim.height, 400);
            return dim;
        }

        private Dimension computePreferredSize(DefaultMutableTreeNode node) {

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


        private JTree getOptionTree() {
            if (optionTree == null) {
                optionTree = new JTree();
                optionTree.addTreeSelectionListener(e -> {
                    TreePath path = e.getNewLeadSelectionPath();

                    if (path != null) {
                        Object node = path.getLastPathComponent();
                        if (node instanceof OptionContentNode) {
                            getSplitPane()
                                    .setRightComponent(((OptionContentNode) node).getComponent());

                        }
                    }
                });
            }
            return optionTree;
        }

        private JSplitPane getSplitPane() {
            if (splitPane == null) {

                splitPane = new JSplitPane();
                splitPane.setAlignmentX(LEFT_ALIGNMENT);
                splitPane.setLeftComponent(new JScrollPane(getOptionTree()));
                splitPane.setRightComponent(getOptionPanel());
                // splitPane.setResizeWeight(0.2);
            }
            return splitPane;

        }

        private JPanel getOptionPanel() {
            if (optionPanel == null) {
                optionPanel = new JPanel();
            }
            return optionPanel;
        }
    }
}
