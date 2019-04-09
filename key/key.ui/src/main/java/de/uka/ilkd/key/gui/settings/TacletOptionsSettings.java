package de.uka.ilkd.key.gui.settings;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.KeYIcons;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import net.miginfocom.layout.AC;
import net.miginfocom.layout.CC;
import net.miginfocom.layout.LC;
import net.miginfocom.swing.MigLayout;
import org.key_project.util.java.ObjectUtil;

import javax.swing.*;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.*;
import java.util.stream.Collectors;

public class TacletOptionsSettings extends JPanel implements SettingsProvider {
    private static final String EXPLANATIONS_RESOURCE = "/de/uka/ilkd/key/gui/help/choiceExplanations.xml";
    private static Properties explanationMap;
    private ChoiceSettings settings;
    private HashMap<String, String> category2DefaultChoice;
    private HashMap<String, Set<String>> category2Choices;
    private boolean changed = false;

    public TacletOptionsSettings() {
        setLayout(new MigLayout(
                new LC().fillX(),
                new AC().fill().grow().gap("3mm")
        ));
        setFocusable(true);
        setChoiceSettings(ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
    }

    /**
     * <p>
     * Returns the explanation for the given category.
     * </p>
     * <p>
     * This method should be public and static because it is independent
     * from the {@link JDialog} and it is also used by the eclipse projects.
     * </p>
     *
     * @param category The category for which the explanation is requested.
     * @return The explanation for the given category.
     */
    public static String getExplanation(String category) {
        synchronized (TacletOptionsSettings.class) {
            if (explanationMap == null) {
                explanationMap = new Properties();
                InputStream is = TacletOptionsSettings.class.getResourceAsStream(EXPLANATIONS_RESOURCE);
                try {
                    if (is == null) {
                        throw new FileNotFoundException(EXPLANATIONS_RESOURCE + " not found");
                    }
                    explanationMap.loadFromXML(is);
                } catch (InvalidPropertiesFormatException e) {
                    System.err.println("Cannot load help message in rule view (malformed XML).");
                    e.printStackTrace();
                } catch (IOException e) {
                    System.err.println("Cannot load help messages in rule view.");
                    e.printStackTrace();
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
     * @return {@code true} proof will be unsound, {@code false} proof will be
     * sound as long as all other choices are sound.
     */
    public static boolean isUnsound(String choice) {
        return "runtimeExceptions:ignore".equals(choice) ||
                "initialisation:disableStaticInitialisation".equals(choice) ||
                "intRules:arithmeticSemanticsIgnoringOF".equals(choice);
    }

    /**
     * Checks if the given choice makes a proof incomplete.
     *
     * @param choice The choice to check.
     * @return {@code true} proof will be incomplete, {@code false} proof will be complete as long as all other choices are complete.
     */
    public static boolean isIncomplete(String choice) {
        return "runtimeExceptions:ban".equals(choice) ||
                "Strings:off".equals(choice) ||
                "intRules:arithmeticSemanticsCheckingOF".equals(choice) ||
                "integerSimplificationRules:minimal".equals(choice) ||
                "programRules:None".equals(choice);
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
     * @param choice  The choice to search.
     * @return The found {@link ChoiceEntry} for the given choice or {@code null} otherwise.
     */
    public static ChoiceEntry findChoice(List<ChoiceEntry> choices, final String choice) {
        return choices.stream().filter(it -> it.getChoice().equals(choice))
                .findAny().orElse(null);
    }

    /**
     * Creates {@link ChoiceEntry}s for all given choices.
     *
     * @param choices The choices.
     * @return The created {@link ChoiceEntry}s.
     */
    public static List<ChoiceEntry> createChoiceEntries(Collection<String> choices) {
        if (choices == null) return Collections.emptyList();
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
        return new ChoiceEntry(choice,
                isUnsound(choice),
                isIncomplete(choice),
                getInformation(choice));
    }

    protected void layoutChoiceSelector() {
        category2DefaultChoice.keySet().stream().sorted().forEach(this::addCategory);
    }

    protected void addCategory(String cat) {
        List<ChoiceEntry> choices = createChoiceEntries(category2Choices.get(cat));
        ChoiceEntry selectedChoice = findChoice(choices, category2DefaultChoice.get(cat));
        String explanation = getExplanation(cat);

        addTitleRow(cat);
        ButtonGroup btnGroup = new ButtonGroup();
        for (ChoiceEntry c : choices) {
            JRadioButton btn = addRadioButton(c, btnGroup);
            if (c.equals(selectedChoice)) {
                btn.setSelected(true);
            }
        }
        addExplanation(explanation);
        /*choiceList.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
                Object selectedValue = choiceList.getSelectedValue();
                if (selectedValue instanceof ChoiceEntry) {
                    setDefaultChoice(((ChoiceEntry) selectedValue).getChoice());
                } else {
                    setDefaultChoice(null);
                }
            }
        });*/
    }

    protected void addExplanation(String explanation) {
        JTextArea explanationArea = new JTextArea();
        explanationArea.setEditable(false);
        explanationArea.setLineWrap(true);
        explanationArea.setWrapStyleWord(true);
        explanationArea.setText(explanation);
        explanationArea.setCaretPosition(0);
        explanationArea.setBackground(getBackground());
        add(explanationArea, new CC().span().newline());
    }

    private JRadioButton addRadioButton(ChoiceEntry c, ButtonGroup btnGroup) {
        Box b = new Box(BoxLayout.X_AXIS);
        JRadioButton button = new JRadioButton(c.choice);
        btnGroup.add(button);
        //add(new JLabel(c.choice));
        b.add(button);

        if (c.incomplete) {
            JLabel lbl = new JLabel(KeYIcons.WARNING_INCOMPLETE.getIcon());
            lbl.setToolTipText("Incomplete");
            b.add(lbl);
        }
        if (c.unsound) {
            JLabel lbl = new JLabel(KeYIcons.WARNING_UNSOUND.getIcon());
            lbl.setToolTipText("Unsound " + button.getToolTipText());
            b.add(lbl);
        }
        if (c.information != null) {
            JLabel lbl = TablePanel.createHelpLabel(c.information);
            b.add(lbl);
        }
        add(b, new CC().newline());
        return button;
    }

    private void addTitleRow(String cat) {
        JLabel lbl = new JLabel(cat);
        add(lbl, new CC().span().newline());
    }

    /**
     * is called to set the selected choice in
     * <code>category2DefaultChoice</code>
     */
    private void setDefaultChoice(String category, String choice) {
        category2DefaultChoice.put(category, choice);
        changed = true;
    }

    @Override
    public String getDescription() {
        return "Taclet Options";
    }

    @Override
    public JComponent getPanel(MainWindow window) {
        setChoiceSettings(SettingsManager.getChoiceSettings(window));
        return this;
    }

    private void setChoiceSettings(ChoiceSettings choiceSettings) {
        this.settings = choiceSettings;
        category2DefaultChoice = settings.getDefaultChoices();
        category2Choices = settings.getChoices();
        removeAll();
        layoutChoiceSelector();
    }

    @Override
    public void applySettings(MainWindow window) throws Exception {
        /*settings.setDefaultChoices(category2DefaultChoice);}*/
        System.out.println("TODO: TacletOptionsSettings.applySettings");
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
         * @param choice      The choice.
         * @param unsound     Is unsound?
         * @param incomplete  Is incomplete?
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
                return choice.equals(other.getChoice()) &&
                        incomplete == other.isIncomplete() &&
                        unsound == other.isUnsound() &&
                        ObjectUtil.equals(information, other.getInformation());
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
                    return choice + " (" + UNSOUND_TEXT + " and " + INCOMPLETE_TEXT + ", " + information + ")";
                } else {
                    return choice + " (" + UNSOUND_TEXT + " and " + INCOMPLETE_TEXT + ")";
                }
            } else if (unsound) {
                if (information != null) {
                    return choice + " (" + UNSOUND_TEXT + ", " + information + ")";
                } else {
                    return choice + " (" + UNSOUND_TEXT + ")";
                }
            } else if (incomplete) {
                if (information != null) {
                    return choice + " (" + INCOMPLETE_TEXT + ", " + information + ")";
                } else {
                    return choice + " (" + INCOMPLETE_TEXT + ")";
                }
            } else {
                if (information != null) {
                    return choice + " (" + information + ")";
                } else {
                    return choice;
                }
            }
        }
    }
}