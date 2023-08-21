/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.settings;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.List;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;

import net.miginfocom.layout.AC;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static java.lang.String.format;

public class TacletOptionsSettings extends SimpleSettingsPanel implements SettingsProvider {
    private static final Logger LOGGER = LoggerFactory.getLogger(TacletOptionsSettings.class);

    private static final long serialVersionUID = 1455572432081960150L;
    private static final String EXPLANATIONS_RESOURCE =
        "/de/uka/ilkd/key/gui/help/choiceExplanations.xml";
    private static Properties explanationMap;
    private HashMap<String, String> category2Choice;
    private HashMap<String, Set<String>> category2Choices;
    private ChoiceSettings settings;
    private boolean warnNoProof = true;

    public TacletOptionsSettings() {
        setHeaderText(getDescription());
        pCenter.setLayout(new MigLayout(new LC().fillX(), new AC().fill().grow().gap("3mm")));
        layoutHead();
        setFocusable(true);
        setChoiceSettings(ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
    }

    /**
     * <p>
     * Returns the explanation for the given category.
     * </p>
     * <p>
     * This method should be public and static because it is independent from the {@link JDialog}
     * and it is also used by the eclipse projects.
     * </p>
     *
     * @param category The category for which the explanation is requested.
     * @return The explanation for the given category.
     */
    public static String getExplanation(String category) {
        synchronized (TacletOptionsSettings.class) {
            if (explanationMap == null) {
                explanationMap = new Properties();
                InputStream is =
                    TacletOptionsSettings.class.getResourceAsStream(EXPLANATIONS_RESOURCE);
                try {
                    if (is == null) {
                        throw new FileNotFoundException(EXPLANATIONS_RESOURCE + " not found");
                    }
                    explanationMap.loadFromXML(is);
                } catch (InvalidPropertiesFormatException e) {
                    LOGGER.error("Cannot load help message in rule view (malformed XML).", e);
                } catch (IOException e) {
                    LOGGER.error("Cannot load help messages in rule view.", e);
                }
            }
        }
        String result = explanationMap.getProperty(category);
        if (result == null) {
            result = "No explanation for " + category + " available.";
        }

        return result;
    }

    /**
     * Checks if the given choice makes a proof unsound.
     *
     * @param choice The choice to check.
     * @return {@code true} proof will be unsound, {@code false} proof will be sound as long as all
     *         other choices are sound.
     */
    public static boolean isUnsound(String choice) {
        return "runtimeExceptions:ignore".equals(choice)
                || "initialisation:disableStaticInitialisation".equals(choice)
                || "intRules:arithmeticSemanticsIgnoringOF".equals(choice);
    }

    /**
     * Checks if the given choice makes a proof incomplete.
     *
     * @param choice The choice to check.
     * @return {@code true} proof will be incomplete, {@code false} proof will be complete as long
     *         as all other choices are complete.
     */
    public static boolean isIncomplete(String choice) {
        return "runtimeExceptions:ban".equals(choice) || "Strings:off".equals(choice)
                || "intRules:arithmeticSemanticsCheckingOF".equals(choice)
                || "integerSimplificationRules:minimal".equals(choice)
                || "programRules:None".equals(choice);
    }

    /**
     * Checks if additional information for the choice are available.
     *
     * @param choice The choice to check.
     * @return The additional information or {@code null} if no information are available.
     */
    public static String getInformation(String choice) {
        if ("JavaCard:on".equals(choice)) {
            return "Sound if a JavaCard program is proven.";
        } else if ("JavaCard:off".equals(choice)) {
            return "Sound if a Java program is proven.";
        } else if ("assertions:on".equals(choice)) {
            return "Sound if JVM is started with enabled assertions for the whole system.";
        } else if ("assertions:off".equals(choice)) {
            return "Sound if JVM is started with disabled assertions for the whole system.";
        } else {
            return null;
        }
    }

    /**
     * Searches the choice in the given {@link ChoiceEntry}s.
     *
     * @param choices The {@link ChoiceEntry}s to search in.
     * @param choice The choice to search.
     * @return The found {@link ChoiceEntry} for the given choice or {@code null} otherwise.
     */
    public static ChoiceEntry findChoice(List<ChoiceEntry> choices, final String choice) {
        return choices.stream().filter(it -> it.getChoice().equals(choice)).findAny().orElse(null);
    }

    /**
     * Creates {@link ChoiceEntry}s for all given choices.
     *
     * @param choices The choices.
     * @return The created {@link ChoiceEntry}s.
     */
    public static List<ChoiceEntry> createChoiceEntries(Collection<String> choices) {
        if (choices == null) {
            return Collections.emptyList();
        }
        return choices.stream().map(TacletOptionsSettings::createChoiceEntry)
                .collect(Collectors.toList());
    }

    /**
     * Creates a {@link ChoiceEntry} for the given choice.
     *
     * @param choice The choice.
     * @return The created {@link ChoiceEntry}.
     */
    public static ChoiceEntry createChoiceEntry(String choice) {
        return new ChoiceEntry(choice, isUnsound(choice), isIncomplete(choice),
            getInformation(choice));
    }

    protected void layoutHead() {
        if (warnNoProof) {
            JLabel lblHead2 = new JLabel("No Proof loaded. Taclet options may not be parsed.");
            lblHead2.setIcon(IconFactory.WARNING_INCOMPLETE.get());
            lblHead2.setFont(lblHead2.getFont().deriveFont(14f));
            pNorth.add(lblHead2);
        }

        JLabel lblHead2 = new JLabel("Taclet options will take effect only on new proofs.");
        lblHead2.setIcon(IconFactory.WARNING_INCOMPLETE.get());
        lblHead2.setFont(lblHead2.getFont().deriveFont(14f));
        pNorth.add(lblHead2);
    }

    protected void layoutChoiceSelector() {
        pCenter.removeAll();
        category2Choice.keySet().stream().sorted().forEach(this::addCategory);
    }

    protected void addCategory(String cat) {
        List<ChoiceEntry> choices = createChoiceEntries(category2Choices.get(cat));
        ChoiceEntry selectedChoice = findChoice(choices, category2Choice.get(cat));
        String explanation = getExplanation(cat);

        addTitleRow(cat);
        ButtonGroup btnGroup = new ButtonGroup();
        for (ChoiceEntry c : choices) {
            JRadioButton btn = addRadioButton(c, btnGroup);
            if (c.equals(selectedChoice)) {
                btn.setSelected(true);
            }
            btn.addActionListener(new ChoiceSettingsSetter(cat, c.choice));
        }
        addExplanation(explanation);
    }

    protected void addExplanation(String explanation) {
        JTextArea explanationArea = new JTextArea();
        explanationArea.setEditable(false);
        explanationArea.setLineWrap(true);
        explanationArea.setWrapStyleWord(true);
        explanationArea.setText(explanation);
        explanationArea.setCaretPosition(0);
        explanationArea.setBackground(getBackground());
        JPanel p = createCollapsibleTitlePane("Info", explanationArea);
        pCenter.add(p, new CC().span().newline());
    }

    @Nonnull
    private JPanel createCollapsibleTitlePane(String titleText, JComponent child) {
        JPanel p = new JPanel(new BorderLayout());
        JPanel north = new JPanel(new BorderLayout());

        p.setBorder(BorderFactory.createLineBorder(Color.black));
        JButton title = new JButton(titleText);
        title.setContentAreaFilled(false);
        title.setBorderPainted(false);
        north.add(title, BorderLayout.WEST);
        p.add(north, BorderLayout.NORTH);
        p.add(child);
        child.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));
        child.setVisible(false);

        title.setIcon(IconFactory.TREE_NODE_RETRACTED.get());
        title.addMouseListener(new MouseAdapter() {
            private boolean opened = false;

            @Override
            public void mouseClicked(MouseEvent e) {
                opened = !opened;
                child.setVisible(opened);
                if (opened) {
                    title.setIcon(IconFactory.TREE_NODE_EXPANDED.get());
                } else {
                    title.setIcon(IconFactory.TREE_NODE_RETRACTED.get());
                }
            }
        });
        return p;
    }

    private JRadioButton addRadioButton(ChoiceEntry c, ButtonGroup btnGroup) {
        Box b = new Box(BoxLayout.X_AXIS);
        JRadioButton button = new JRadioButton(c.choice);
        btnGroup.add(button);
        // add(new JLabel(c.choice));
        b.add(button);

        if (c.incomplete) {
            JLabel lbl = new JLabel(IconFactory.WARNING_INCOMPLETE.get());
            lbl.setToolTipText("Incomplete");
            b.add(lbl);
        }
        if (c.unsound) {
            JLabel lbl = new JLabel(IconFactory.WARNING_UNSOUND.get());
            lbl.setToolTipText("Unsound");
            b.add(lbl);
        }
        if (c.information != null) {
            JLabel lbl = SettingsPanel.createHelpLabel(c.information);
            b.add(lbl);
        }
        pCenter.add(b, new CC().newline());
        return button;
    }

    private void addTitleRow(String cat) {
        JLabel lbl = new JLabel(cat);
        lbl.setFont(lbl.getFont().deriveFont(14f));
        pCenter.add(lbl, new CC().span().newline());
    }

    @Override
    public String getDescription() {
        return "Taclet Options";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        warnNoProof = window.getMediator().getSelectedProof() == null;
        setChoiceSettings(SettingsManager.getChoiceSettings(window));
        return this;
    }

    private void setChoiceSettings(ChoiceSettings choiceSettings) {
        this.settings = choiceSettings;
        category2Choice = new HashMap<>(settings.getDefaultChoices());
        category2Choices = new HashMap<>(settings.getChoices());
        layoutChoiceSelector();
    }

    @Override
    public void applySettings(MainWindow window) {
        settings.setDefaultChoices(category2Choice);
    }

    /**
     * Represents a choice with all its meta information.
     *
     * @author Martin Hentschel
     */
    public static class ChoiceEntry {
        /**
         * Text shown to the user in case of incompletness.
         */
        public static final String INCOMPLETE_TEXT = "incomplete";

        /**
         * Text shown to the user in case of unsoundness.
         */
        public static final String UNSOUND_TEXT = "Java modeling unsound";

        /**
         * The choice.
         */
        private final String choice;

        /**
         * Is unsound?
         */
        private final boolean unsound;

        /**
         * Is incomplete?
         */
        private final boolean incomplete;

        /**
         * An optionally information.
         */
        private final String information;

        /**
         * Constructor.
         *
         * @param choice The choice.
         * @param unsound Is unsound?
         * @param incomplete Is incomplete?
         * @param information An optionally information.
         */
        public ChoiceEntry(String choice, boolean unsound, boolean incomplete, String information) {
            assert choice != null;
            this.choice = choice;
            this.unsound = unsound;
            this.incomplete = incomplete;
            this.information = information;
        }

        /**
         * Returns the choice.
         *
         * @return The choice.
         */
        public String getChoice() {
            return choice;
        }

        /**
         * Checks for soundness.
         *
         * @return {@code true} unsound, {@code false} sound.
         */
        public boolean isUnsound() {
            return unsound;
        }

        /**
         * Checks for completeness.
         *
         * @return {@code true} incomplete, {@code false} complete.
         */
        public boolean isIncomplete() {
            return incomplete;
        }

        /**
         * Returns the optionally information.
         *
         * @return The optionally information.
         */
        public String getInformation() {
            return information;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int hashCode() {
            int hashcode = 5;
            hashcode = hashcode * 17 + choice.hashCode();
            hashcode = hashcode * 17 + (incomplete ? 5 : 3);
            hashcode = hashcode * 17 + (unsound ? 5 : 3);
            if (information != null) {
                hashcode = hashcode * 17 + information.hashCode();
            }
            return hashcode;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean equals(Object obj) {
            if (obj instanceof ChoiceEntry) {
                ChoiceEntry other = (ChoiceEntry) obj;
                return choice.equals(other.getChoice()) && incomplete == other.isIncomplete()
                        && unsound == other.isUnsound()
                        && Objects.equals(information, other.getInformation());
            } else {
                return false;
            }
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            if (unsound && incomplete) {
                if (information != null) {
                    return format("%s (%s and %s, %s)", choice, UNSOUND_TEXT, INCOMPLETE_TEXT,
                        information);
                } else {
                    return format("%s (%s and %s)", choice, UNSOUND_TEXT, INCOMPLETE_TEXT);
                }
            } else if (unsound) {
                if (information != null) {
                    return format("%s (%s, %s)", choice, UNSOUND_TEXT, information);
                } else {
                    return format("%s (%s)", choice, UNSOUND_TEXT);
                }
            } else if (incomplete) {
                if (information != null) {
                    return format("%s (%s, %s)", choice, INCOMPLETE_TEXT, information);
                } else {
                    return format("%s (%s)", choice, INCOMPLETE_TEXT);
                }
            } else {
                if (information != null) {
                    return format("%s (%s)", choice, information);
                } else {
                    return choice;
                }
            }
        }
    }

    private class ChoiceSettingsSetter implements ActionListener {
        private final String category;
        private final String options;

        public ChoiceSettingsSetter(String cat, String choice) {
            category = cat;
            options = choice;
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            category2Choice.put(category, options);
        }
    }
}
