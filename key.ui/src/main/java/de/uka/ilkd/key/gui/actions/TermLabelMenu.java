/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.util.*;
import java.util.List;
import java.util.Map.Entry;
import javax.swing.*;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerEvent;
import de.uka.ilkd.key.control.event.TermLabelVisibilityManagerListener;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.logic.Name;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This menu can be used to toggle TermLabel visibility for the SequentView.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
@NullMarked
public class TermLabelMenu extends JMenu {
    public static final String TERM_LABEL_MENU = "Term Labels";

    /**
     *
     */
    private static final long serialVersionUID = 1L;
    private final TermLabelVisibilityManager visibleTermLabels = new TermLabelVisibilityManager();
    private final Map<Name, TermLabelCheckBox> checkBoxMap = new TreeMap<>();
    private final MainWindow mainWindow;
    private final DisplayLabelsCheckBox displayLabelsCheckBox;

    /**
     * Observes changes on {@link #visibleTermLabels}.
     * <p>
     * The bound method reference binds {@code this} while the receiver is still under
     * initialization (EISOP initialization check); safe here since the listener only ever fires
     * after construction completes, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:methodref.receiver.bound.invalid")
    private final TermLabelVisibilityManagerListener termLabelVisibilityManagerListener =
        this::handleVisibleLabelsChanged;

    /**
     * The menu-configuration calls, the listener registration and the {@link #rebuildMenu()} call
     * below operate on {@code this} while the receiver is still under initialization (EISOP
     * initialization check); safe here since these configure the local menu and the listeners
     * only react to later events, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public TermLabelMenu(final MainWindow mainWindow) {
        this.mainWindow = mainWindow;
        setText(TERM_LABEL_MENU);
        setToolTipText("Configure term label visibility.");
        visibleTermLabels.addTermLabelVisibilityManagerListener(termLabelVisibilityManagerListener);

        displayLabelsCheckBox = new DisplayLabelsCheckBox(mainWindow);

        rebuildMenu();

        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {

            /*
             * Change font style for TermLabelCheckBox instances when the selected node changes.
             */
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
                Set<Name> labelNames =
                    getOccuringTermLabels(mainWindow.getMediator().getSelectedNode().sequent());
                for (Entry<Name, TermLabelCheckBox> entry : checkBoxMap.entrySet()) {
                    TermLabelCheckBox checkBox = entry.getValue();
                    /*
                     * Font style indicates whether a label occurs in the currently displayed
                     * sequent.
                     */
                    if (labelNames.contains(entry.getKey())) {
                        checkBox.setBoldFont();
                    } else {
                        checkBox.setItalicFont();
                    }
                }
            }

            /*
             * Returns names of TermLabels, that occur in this sequent.
             */
            public Set<Name> getOccuringTermLabels(Sequent seq) {
                final Set<Name> result = new HashSet<>();
                for (final SequentFormula sf : seq) {
                    result.addAll(getLabelsForTermRecursively((JTerm) sf.formula()));
                }
                return result;
            }

            /*
             * Returns names of TermLabels, that occur in term or one of its subterms.
             */
            private static Set<Name> getLabelsForTermRecursively(JTerm term) {
                Set<Name> result = new HashSet<>();

                if (term.hasLabels()) {
                    for (TermLabel label : term.getLabels()) {
                        result.add(label.name());
                    }
                }

                for (final JTerm subTerm : term.subs()) {
                    result.addAll(getLabelsForTermRecursively(subTerm));
                }

                return result;
            }

            /*
             * This function only has effect if the Profile gets changed.
             */
            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> e) {
                rebuildMenu();
            }
        });
    }

    /**
     * When the visible term labels have changed.
     * <p>
     * <b>Attention:</b> This can happen in an Eclipse context outside of the checkbox items!
     *
     * @param e The event object.
     */
    protected void handleVisibleLabelsChanged(TermLabelVisibilityManagerEvent e) {
        if (displayLabelsCheckBox != null) {
            displayLabelsCheckBox.setSelected(visibleTermLabels.isShowLabels());
        }
        for (TermLabelCheckBox box : checkBoxMap.values()) {
            box.setEnabled(visibleTermLabels.isShowLabels());
            box.setSelected(!visibleTermLabels.isHidden(box.labelName));
        }
        mainWindow.makePrettyView();
    }

    private void rebuildMenu() {
        removeAll();
        add(displayLabelsCheckBox);
        addSeparator();

        /*
         * Get sorted list of term label names.
         */
        List<Name> labelNames = mainWindow.getSortedTermLabelNames();

        /*
         * Create list of {@link TermLabelCheckBox} instances.
         */
        ArrayList<TermLabelCheckBox> checkBoxList = new ArrayList<>();
        for (Name labelName : labelNames) {
            TermLabelCheckBox checkBox = checkBoxMap.get(labelName);
            if (checkBox == null) {
                checkBox = new TermLabelCheckBox(labelName);
                checkBoxMap.put(labelName, checkBox);
            }
            checkBoxList.add(checkBox);
        }

        /*
         * Add the checkboxes to the menu.
         */
        for (TermLabelCheckBox c : checkBoxList) {
            add(c);
        }
    }

    public TermLabelVisibilityManager getVisibleTermLabels() {
        return visibleTermLabels;
    }

    public class DisplayLabelsCheckBox extends KeYMenuCheckBox {
        public static final String LABEL = "Display Term Labels in Formulas";

        public static final String TOOL_TIP =
            "Use this checkbox to toggle visibility for all term labels.";

        /**
         *
         */
        private static final long serialVersionUID = 8766949321781919880L;

        /**
         * The action-configuration setters below operate on {@code this} while the receiver is
         * still under initialization (EISOP initialization check); safe here, suppressed with a
         * scoped key.
         */
        @SuppressWarnings("nullness:method.invocation.invalid")
        private DisplayLabelsCheckBox(MainWindow mainWindow) {
            super(mainWindow, LABEL, true);
            setTooltip(TOOL_TIP);
            setName("DisplayLabelsCheckBox");
            setSelected(visibleTermLabels.isShowLabels());
        }

        @Override
        public void handleClickEvent() {
            boolean selected = isSelected();
            visibleTermLabels.setShowLabels(selected);
            for (JCheckBoxMenuItem checkBox : checkBoxMap.values()) {
                checkBox.setEnabled(selected);
            }
            mainWindow.makePrettyView();
        }

        @Override
        public final void setSelected(boolean b) {
            super.setSelected(b);
            handleClickEvent();
        }
    }

    private class TermLabelCheckBox extends KeYMenuCheckBox {

        /**
         *
         */
        private static final long serialVersionUID = 4582177241207958225L;

        // The name of the label, which belongs to this checkbox.
        private final Name labelName;

        // This String is used as ToolTipText in case the CheckBox is enabled.
        private @Nullable String enabledToolTipText = null;

        /**
         * The action-configuration calls and the preference handling below operate on
         * {@code this} while the receiver is still under initialization (EISOP initialization
         * check); safe here since these configure the local check box only, suppressed with
         * scoped keys.
         */
        @SuppressWarnings({ "nullness:method.invocation.invalid",
            "nullness:argument.type.incompatible" })
        TermLabelCheckBox(Name labelName) {
            super(mainWindow, labelName.toString(), true);
            this.labelName = labelName;
            setName(labelName.toString());
            setSelected(!visibleTermLabels.isHidden(labelName));
            setEnabled(displayLabelsCheckBox.isSelected());
            mainWindow.loadPreferences(this);
            visibleTermLabels.setHidden(labelName, !isSelected());
            setItalicFont();
        }

        @Override
        public void handleClickEvent() {
            visibleTermLabels.setHidden(labelName, !isSelected());
            mainWindow.makePrettyView();
        }

        @Override
        public final void setEnabled(boolean b) {
            super.setEnabled(b);
            updateToolTipText();
        }

        private void setItalicFont() {
            Font font = getFont();
            if (font != null) {
                setFont(font.deriveFont(Font.ITALIC));
            }
            setEnabledToolTipText(
                "Term label " + labelName + " does not occur in the current sequent.");
        }

        private void setBoldFont() {
            Font font = getFont();
            if (font != null) {
                setFont(font.deriveFont(Font.BOLD));
            }
            setEnabledToolTipText("Click to toggle visibility for term label " + labelName + ".");
        }

        /*
         * Define the text which is used in case this CheckBox is enabled.
         */
        private void setEnabledToolTipText(String s) {
            enabledToolTipText = s;
            updateToolTipText();
        }

        /*
         * Call this method in case ToolTipText needs to be updated.
         */
        private void updateToolTipText() {
            if (isEnabled()) {
                String text = enabledToolTipText;
                // {@code enabledToolTipText} is only ever {@code null} before the first
                // {@link #setEnabledToolTipText} call; show the disabled hint in that impossible
                // intermediate state.
                setToolTipText(text == null
                        ? "You turned off visibility for all term labels. This checkbox is disabled."
                        : text);
            } else {
                setToolTipText("You turned off visibility for all term labels. "
                    + "This checkbox is disabled.");
            }
        }

    }
}
