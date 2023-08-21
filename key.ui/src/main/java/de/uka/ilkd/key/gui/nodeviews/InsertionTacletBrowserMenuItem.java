/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public abstract class InsertionTacletBrowserMenuItem extends JMenu implements TacletMenuItem {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(InsertionTacletBrowserMenuItem.class);

    /**
     *
     */
    private static final long serialVersionUID = 1874640339950617746L;
    /**
     * The number of items that are to be shown in the dialog before a message referring to the
     * dialog is issued. There are always "Open Dialog" and a {@link JSeparator}"
     */
    private static final int MAX_ITEM_NUMBER = 30;
    /** all taclet apps the user can choose from */
    private final Collection<TacletAppListItem> insertionTaclets;
    /** the added action listeners */
    private final List<ActionListener> listenerList = new LinkedList<>();
    /** the notation info to pretty print the taclet apps */
    protected final NotationInfo notInfo;
    /** the parent frame of the selection dialog to be displayed */
    protected final JFrame parent;
    /** the selected taclet to be applied */
    private TacletApp selectedTaclet;
    /** the services */
    protected final Services services;

    /** the base title; used title = basetitle + ( nrOfItems ) */
    private final String baseTitle;

    public InsertionTacletBrowserMenuItem(String title, JFrame parent, NotationInfo notInfo,
            Services services) {

        super(title);
        this.baseTitle = title;
        this.parent = parent;
        this.notInfo = notInfo;
        this.services = services;

        insertionTaclets = createInsertionList();

        final JMenuItem menuItem = new JMenuItem("Open Dialog");
        menuItem.addActionListener(e -> openDialog());

        menuItem.setToolTipText("Browse applicable taclets.");

        add(menuItem);
        addSeparator();
    }

    /**
     * @return the list where the tacletappItems are stored (allows easy exchange for e.g. a sorted
     *         list) default: is filo
     */
    protected Collection<TacletAppListItem> createInsertionList() {
        return new LinkedList<>();
    }

    /**
     * Adds a new taclet to be displayed by this component it is assumed that the app has been
     * tested before by {@link #isResponsible}.
     *
     * @param app the TacletApp to be added
     */
    public void add(TacletApp app) {
        insertionTaclets.add(createListItem(app));

        if (getItemCount() >= MAX_ITEM_NUMBER) {
            if (getItemCount() == MAX_ITEM_NUMBER) {
                JLabel l = new JLabel("For more hidden formulas, see 'Open Dialog'");
                l.setFont(l.getFont().deriveFont(Font.ITALIC));
                add(l);
            }
            return;
        }

        final DefaultTacletMenuItem appItem =
            new DefaultTacletMenuItem(app, notInfo, services);
        appItem.addActionListener(this::processTacletSelected);
        add(appItem);
        setText(baseTitle + " (" + getAppSize() + (getAppSize() != 1 ? " items" : " item") + ")");
    }

    @Override
    public void addActionListener(ActionListener listener) {
        listenerList.add(listener);
    }

    protected abstract Sequent checkTaclet(Taclet t);

    /** @return the selected taclet to be applied */
    public TacletApp connectedTo() {
        return selectedTaclet;
    }

    public int getAppSize() {
        return insertionTaclets.size();
    }

    /**
     * tests if this class is responsible for the given taclet
     *
     * @param t the Taclet to be checked
     * @return true if this item implementation shall be used
     */
    public boolean isResponsible(Taclet t) {
        return checkTaclet(t) != null;
    }

    /**
     * opens the selection dialog displaying all hidden formulas in a list and allowing the user to
     * select the one to be added
     */
    public void openDialog() {
        final JDialog dialog = new JDialog(parent, getText(), true);

        final JList<TacletAppListItem> selectionList =
            new JList<>(insertionTaclets.toArray(new TacletAppListItem[0]));

        final JScrollPane scrollPane =
            new JScrollPane(selectionList, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED,
                ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        scrollPane.setPreferredSize(new Dimension(300, 100));
        scrollPane.setMinimumSize(new Dimension(150, 50));


        selectionList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);

        if (getAppSize() > 0) { // should always be true
            selectionList.setSelectedIndex(0);
        }


        final JTextArea displayHiddenFormula = new JTextArea();

        final TacletAppListItem selectedValue = selectionList.getSelectedValue();
        displayHiddenFormula.setText(selectedValue == null ? "" : selectedValue.longDescription());

        displayHiddenFormula.setCaretPosition(0);

        displayHiddenFormula.setEditable(false);

        selectionList.addListSelectionListener(e -> {
            if (e.getSource() instanceof JList) {
                final JList<?> list = (JList<?>) e.getSource();
                if (list.getSelectedIndex() >= 0) {
                    if (list.getSelectedValue() instanceof TacletAppListItem) {
                        displayHiddenFormula.setText(
                            ((TacletAppListItem) list.getSelectedValue()).longDescription());
                    }
                } else {
                    displayHiddenFormula.setText("");
                }
                displayHiddenFormula.setCaretPosition(0);
            }
        });

        final JScrollPane formulaDisplaySP = new JScrollPane(displayHiddenFormula);

        final JSplitPane split =
            new JSplitPane(JSplitPane.HORIZONTAL_SPLIT, scrollPane, formulaDisplaySP) {
                /**
                 *
                 */
                private static final long serialVersionUID = -6688343484818325411L;

                public void setUI(javax.swing.plaf.SplitPaneUI ui) {
                    try {
                        super.setUI(ui);
                    } catch (NullPointerException e) {
                        LOGGER.debug("Exception thrown by class Main at setUI");
                    }
                }
            }; // work around bug in
               // com.togethersoft.util.ui.plaf.metal.OIMetalSplitPaneUI
        selectedTaclet = null;

        final JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(e -> {
            selectedTaclet = null;
            dialog.setVisible(false);
            dialog.dispose();
        });

        final JButton applyButton = new JButton("Apply");
        applyButton.addActionListener(e -> {
            final TacletAppListItem selectedItem = selectionList.getSelectedValue();

            if (selectedItem == null) { // should never be true
                selectedTaclet = null;
            } else {
                selectedTaclet = selectedItem.getTacletApp();
            }

            dialog.setVisible(false);
            dialog.dispose();
            processTacletSelected(new ActionEvent(InsertionTacletBrowserMenuItem.this, 0, ""));
        });

        final JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout());

        buttonPanel.add(applyButton);
        buttonPanel.add(cancelButton);

        dialog.getContentPane().setLayout(new BorderLayout());

        dialog.getContentPane().add(split, BorderLayout.CENTER);
        dialog.getContentPane().add(buttonPanel, BorderLayout.SOUTH);

        dialog.setSize(500, 250);

        dialog.setVisible(true);
    }

    protected void processTacletSelected(ActionEvent e) {
        for (final ActionListener al : listenerList) {
            al.actionPerformed(e);
        }
    }

    @Override
    public void removeActionListener(ActionListener listener) {
        listenerList.remove(listener);
    }

    public TacletAppListItem createListItem(TacletApp app) {
        return new TacletAppListItem(app, checkTaclet(app.taclet()), notInfo, services);
    }

    /**
     * inner class to pretty print the formulas to be added
     */
    static class TacletAppListItem {
        private final TacletApp app;
        private final NotationInfo notInfo;
        private final Services services;
        private final Sequent seq;

        public TacletAppListItem(TacletApp app, Sequent seq, NotationInfo notInfo,
                Services services) {
            this.app = app;
            this.seq = seq;
            this.notInfo = notInfo;
            this.services = services;
        }

        public TacletApp getTacletApp() {
            return app;
        }

        public String shortDescription() {
            return longDescription();
        }

        public String longDescription() {
            final LogicPrinter printer = LogicPrinter.purePrinter(notInfo, services);
            printer.setInstantiation(app.instantiations());
            printer.printSequent(seq);
            return printer.result();
        }

        @Override
        public String toString() {
            return longDescription();
        }
    }

}
