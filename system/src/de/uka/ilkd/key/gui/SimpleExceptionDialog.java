// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import javax.swing.JDialog;

import javax.swing.JPanel;
import java.awt.GridBagLayout;
import java.awt.Dimension;
import javax.swing.JTextArea;
import java.awt.GridBagConstraints;
import javax.swing.JCheckBox;
import javax.swing.JButton;
import javax.swing.JScrollPane;

import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

public class SimpleExceptionDialog extends JDialog {
        private static final long serialVersionUID = 1L;
        public final static SimpleExceptionDialog INSTANCE = new SimpleExceptionDialog();

        private JPanel jPanel = null; // @jve:decl-index=0:visual-constraint="279,56"
        private JTextArea jTextArea = null;
        private JCheckBox jCheckBox = null;
        private JButton jButton = null;
        private JTextArea jTextArea1 = null;
        private JScrollPane jScrollPane = null;
        private JScrollPane jScrollPane1 = null;

        private GridBagConstraints scrollPaneConst() {
                GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
                gridBagConstraints3.fill = GridBagConstraints.BOTH;
                gridBagConstraints3.gridy = 2;
                gridBagConstraints3.weightx = 1.0;
                gridBagConstraints3.weighty = 1.0;
                gridBagConstraints3.gridwidth = 2;
                gridBagConstraints3.gridx = 0;
                return gridBagConstraints3;
        }

        /**
         * This method initializes jPanel
         * 
         * @return javax.swing.JPanel
         */
        private JPanel getJPanel() {
                if (jPanel == null) {

                        GridBagConstraints gridBagConstraints = new GridBagConstraints();
                        gridBagConstraints.fill = GridBagConstraints.BOTH;
                        gridBagConstraints.gridy = 0;
                        gridBagConstraints.weightx = 1.0;
                        gridBagConstraints.weighty = 1.0;
                        gridBagConstraints.gridwidth = 2;
                        gridBagConstraints.gridx = 0;
                        GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
                        gridBagConstraints2.gridx = 1;
                        gridBagConstraints2.anchor = GridBagConstraints.EAST;
                        gridBagConstraints2.ipadx = 0;
                        gridBagConstraints2.insets = new Insets(5, 0, 5, 5);
                        gridBagConstraints2.weighty = 0.0;
                        gridBagConstraints2.ipady = 0;
                        gridBagConstraints2.gridy = 1;
                        GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
                        gridBagConstraints1.gridx = 0;
                        gridBagConstraints1.insets = new Insets(0, 5, 0, 0);
                        gridBagConstraints1.gridy = 1;
                        jPanel = new JPanel();
                        jPanel.setLayout(new GridBagLayout());
                        jPanel.setSize(new Dimension(548, 222));
                        jPanel.add(getJCheckBox(), gridBagConstraints1);
                        jPanel.add(getJButton(), gridBagConstraints2);
                        jPanel.add(getJScrollPane(), gridBagConstraints);
                }
                return jPanel;
        }

        /**
         * This method initializes jTextArea
         * 
         * @return javax.swing.JTextArea
         */
        private JTextArea getJTextArea() {
                if (jTextArea == null) {
                        jTextArea = new JTextArea();
                }
                return jTextArea;
        }

        /**
         * This method initializes jCheckBox
         * 
         * @return javax.swing.JCheckBox
         */
        private JCheckBox getJCheckBox() {
                if (jCheckBox == null) {
                        jCheckBox = new JCheckBox();
                        jCheckBox.setText("Show Details");
                        jCheckBox.addActionListener(new ActionListener() {

                                public void actionPerformed(ActionEvent e) {
                                        if (!jCheckBox.isSelected()) {
                                                getJPanel().remove(
                                                                getJScrollPane1());
                                        } else {
                                                getJPanel().add(getJScrollPane1(),
                                                                scrollPaneConst());
                                        }
                                        SimpleExceptionDialog.this.pack();
                                        SimpleExceptionDialog.this.repaint();

                                }
                        });
                }
                return jCheckBox;
        }

        /**
         * This method initializes jButton
         * 
         * @return javax.swing.JButton
         */
        private JButton getJButton() {
                if (jButton == null) {
                        jButton = new JButton();
                        jButton.setText("Close");
                        jButton.addActionListener(new ActionListener() {

                                public void actionPerformed(ActionEvent e) {
                                        setVisible(false);

                                }
                        });
                }
                return jButton;
        }

        /**
         * This method initializes jTextArea1
         * 
         * @return javax.swing.JTextArea
         */
        private JTextArea getJTextArea1() {
                if (jTextArea1 == null) {
                        jTextArea1 = new JTextArea();
                }
                return jTextArea1;
        }

        /**
         * This method initializes jScrollPane
         * 
         * @return javax.swing.JScrollPane
         */
        private JScrollPane getJScrollPane() {
                if (jScrollPane == null) {
                        jScrollPane = new JScrollPane();
                        jScrollPane.setViewportView(getJTextArea());
                }
                return jScrollPane;
        }

        /**
         * This method initializes jScrollPane1
         * 
         * @return javax.swing.JScrollPane
         */
        private JScrollPane getJScrollPane1() {
                if (jScrollPane1 == null) {
                        jScrollPane1 = new JScrollPane();
                        jScrollPane1.setViewportView(getJTextArea1());

                }
                return jScrollPane1;
        }

        private SimpleExceptionDialog() {
                this.add(getJPanel());
                this.setMinimumSize(new Dimension(400, 150));
                this.setLocationByPlatform(true);
                pack();
        }
        
        

        public void showDialog(String title, String description, Throwable e) {
                String details = "Exception:\n " + e.toString() + "\n\n";
                details += "Stacktrace:\n";
                for (StackTraceElement el : e.getStackTrace()) {
                        details += el.toString() + "\n";
                }
                showDialog(title, description, details);
        }

        public void showDialog(String title, String description, String details) {
                this.setTitle(title);
                getJTextArea().setText(description);
                getJTextArea1().setText(details);
                this.setModal(true);
                this.setVisible(true);
        }

}