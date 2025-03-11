/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.*;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.lemmatagenerator.ItemChooser.ItemFilter;
import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletFilter;
import de.uka.ilkd.key.taclettranslation.lemma.TacletSoundnessPOLoader.TacletInfo;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * The core of the Selection-Dialog is the class SelectionPanel which extends JPanel. It contains a
 * table for presenting the taclets using special filters. The dialog owns two SelectionPanels, one
 * for presenting the taclets that can be chosen by the user (), and one for presenting the taclets
 * that the user has chosen. Both tables work on the same model but using different filters: A
 * taclet is wrapped by an object of type TableItem which contains the taclet itself and a
 * additional information about on which side it should be shown (LEFT or RIGHT). The taclet
 *
 */
public class LemmaSelectionDialog extends JDialog implements TacletFilter {

    private static final long serialVersionUID = 1L;

    private JButton okButton;
    private JCheckBox showSupported;
    private JButton cancelButton;
    private JPanel buttonPanel;
    private JPanel contentPanel;
    private ItemChooser<TacletInfo> tacletChooser;
    private final ItemFilter<TacletInfo> showOnlySupportedTaclets =
        itemData -> !itemData.isNotSupported();

    private final ItemFilter<TacletInfo> filterForMovingTaclets =
        itemData -> !itemData.isNotSupported() && !itemData.isAlreadyInUse();


    public LemmaSelectionDialog() {
        super(MainWindow.getInstance());
        this.setTitle("Taclet Selection");
        this.setLayout(new BoxLayout(this.getContentPane(), BoxLayout.X_AXIS));
        this.getContentPane().add(Box.createHorizontalStrut(10));
        this.getContentPane().add(getContentPanel());
        this.getContentPane().add(Box.createHorizontalStrut(10));
        this.setMinimumSize(new Dimension(300, 300));
        this.pack();
        this.setLocationRelativeTo(MainWindow.getInstance());
    }

    public ImmutableSet<Taclet> showModal(List<TacletInfo> taclets) {
        this.setModal(true);
        this.getTacletChooser().setItems(taclets, "Taclets");
        this.setVisible(true);
        ImmutableSet<Taclet> set = DefaultImmutableSet.nil();
        for (TacletInfo info : getTacletChooser().getDataOfSelectedItems()) {
            set = set.add(info.getTaclet());
        }
        return set;
    }

    private JCheckBox getShowSupported() {
        if (showSupported == null) {
            showSupported = new JCheckBox("Show only supported taclets.");
            showSupported.setSelected(true);
            showSupported.addActionListener(e -> {
                if (showSupported.isSelected()) {
                    getTacletChooser().addFilter(showOnlySupportedTaclets);

                } else {
                    getTacletChooser().removeFilter(showOnlySupportedTaclets);

                }

            });
        }
        return showSupported;
    }

    private JPanel getButtonPanel() {

        if (buttonPanel == null) {
            buttonPanel = new JPanel();
            buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
            buttonPanel.add(getShowSupported());
            buttonPanel.add(Box.createHorizontalGlue());
            buttonPanel.add(getOkButton());
            buttonPanel.add(Box.createHorizontalStrut(8));

            buttonPanel.add(getCancelButton());
        }
        return buttonPanel;
    }

    private JPanel getContentPanel() {
        if (contentPanel == null) {
            contentPanel = new JPanel();
            contentPanel.setLayout(new BoxLayout(contentPanel, BoxLayout.Y_AXIS));
            contentPanel.add(Box.createVerticalStrut(10));
            contentPanel.add(getTacletChooser());
            contentPanel.add(getButtonPanel());
            contentPanel.add(Box.createVerticalStrut(10));
        }
        return contentPanel;
    }

    private JButton getOkButton() {
        if (okButton == null) {
            okButton = new JButton("OK");
            okButton.addActionListener(e -> tacletsSelected());
            okButton.setPreferredSize(getCancelButton().getPreferredSize());
        }
        return okButton;
    }



    private void tacletsSelected() {

        dispose();
    }

    private void cancel() {
        getTacletChooser().removeSelection();
        getTacletChooser().moveAllToLeft();
        dispose();
    }

    private JButton getCancelButton() {
        if (cancelButton == null) {
            cancelButton = new JButton("Cancel");
            cancelButton.addActionListener(e -> cancel());
            GuiUtilities.attachClickOnEscListener(cancelButton);
        }
        return cancelButton;
    }

    private ItemChooser<TacletInfo> getTacletChooser() {
        if (tacletChooser == null) {
            tacletChooser = new ItemChooser<>("Search for taclets with names containing");
            tacletChooser.addFilterForMovingItems(filterForMovingTaclets);
            tacletChooser.addFilter(showOnlySupportedTaclets);
        }
        return tacletChooser;
    }

    @Override
    public ImmutableSet<Taclet> filter(List<TacletInfo> taclets) {

        return showModal(taclets);
    }

}
