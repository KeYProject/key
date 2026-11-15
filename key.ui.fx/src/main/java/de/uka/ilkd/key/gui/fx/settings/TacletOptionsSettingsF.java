/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.settings;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.stream.Collectors;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.ContentDisplay;
import javafx.scene.control.Label;
import javafx.scene.control.RadioButton;
import javafx.scene.control.TitledPane;
import javafx.scene.control.ToggleGroup;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;

import de.uka.ilkd.key.gui.fx.MainWindowF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF;
import de.uka.ilkd.key.gui.fx.fonticons.IconFactoryF.Key;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Settings provider for the taclet options, counter-part of
 * {@code de.uka.ilkd.key.gui.settings.TacletOptionsSettings} of the Swing module {@code key.ui}.
 * <p>
 * The panel shows one collapsible section ({@link TitledPane}) per choice category with a radio
 * button per available choice, marked with an incomplete ({@link Key#WARNING_INCOMPLETE}) or
 * unsound ({@link Key#WARNING_UNSOUND}) icon if applicable, followed by the explanation of the
 * category (from the shared {@code choiceExplanations.xml} resource, see
 * {@link #getExplanation(String)}).
 * <p>
 * Like the Swing original, the radio buttons are only shown when a proof is loaded (Swing hides
 * them together with the "No Proof loaded" hint staying visible); the warning that the options
 * take effect only on new proofs is always shown, and the section title warns if the current
 * choice differs from the loaded proof.
 * <p>
 * Applying writes the edited choices through to the global default choice settings,
 * {@link ProofSettings#DEFAULT_SETTINGS}; that is what loading a problem reads to build a new
 * proof (Swing {@code TacletOptionsSettings.applySettings}).
 */
public class TacletOptionsSettingsF extends SettingsPanelF implements SettingsProviderF {

    private static final Logger LOGGER = LoggerFactory.getLogger(TacletOptionsSettingsF.class);

    /**
     * the explanations resource, shared with the Swing UI (Swing
     * {@code TacletOptionsSettings.EXPLANATIONS_RESOURCE})
     */
    private static final String EXPLANATIONS_RESOURCE =
        "/de/uka/ilkd/key/gui/help/choiceExplanations.xml";

    private static Properties explanationMap;

    private final Map<String, String> category2Choice = new HashMap<>();
    private final Map<String, Set<String>> category2Choices = new HashMap<>();

    private boolean warnNoProof = true;

    private Proof loadedProof = null;

    public TacletOptionsSettingsF() {
        setHeaderText(getDescription());
        setChoiceSettings(ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
    }

    /**
     * <p>
     * Returns the explanation for the given category.
     * </p>
     * <p>
     * This method is public and static because it is independent from the dialog and it is also
     * used outside (Swing {@code TacletOptionsSettings.getExplanation}).
     * </p>
     *
     * @param category the category for which the explanation is requested
     * @return the explanation for the given category
     */
    public static String getExplanation(String category) {
        synchronized (TacletOptionsSettingsF.class) {
            if (explanationMap == null) {
                explanationMap = new Properties();
                InputStream is =
                    TacletOptionsSettingsF.class.getResourceAsStream(EXPLANATIONS_RESOURCE);
                try {
                    if (is == null) {
                        throw new FileNotFoundException(EXPLANATIONS_RESOURCE + " not found");
                    }
                    explanationMap.loadFromXML(is);
                } catch (IllegalArgumentException e) {
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
     * Checks if the given choice makes a proof unsound (Swing
     * {@code TacletOptionsSettings.isUnsound}).
     *
     * @param choice the choice to check
     * @return {@code true} proof will be unsound, {@code false} proof will be sound as long as
     *         all other choices are sound
     */
    public static boolean isUnsound(String choice) {
        return "runtimeExceptions:ignore".equals(choice)
                || "initialisation:disableStaticInitialisation".equals(choice)
                || "intRules:arithmeticSemanticsIgnoringOF".equals(choice);
    }

    /**
     * Checks if the given choice makes a proof incomplete (Swing
     * {@code TacletOptionsSettings.isIncomplete}).
     *
     * @param choice the choice to check
     * @return {@code true} proof will be incomplete, {@code false} proof will be complete as long
     *         as all other choices are complete
     */
    public static boolean isIncomplete(String choice) {
        return "runtimeExceptions:ban".equals(choice) || "Strings:off".equals(choice)
                || "intRules:arithmeticSemanticsCheckingOF".equals(choice)
                || "integerSimplificationRules:minimal".equals(choice)
                || "programRules:None".equals(choice);
    }

    /**
     * Checks if additional information for the choice are available (Swing
     * {@code TacletOptionsSettings.getInformation}).
     *
     * @param choice the choice to check
     * @return the additional information or {@code null} if no information are available
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
     * Searches the choice in the given {@link ChoiceEntry}s (Swing
     * {@code TacletOptionsSettings.findChoice}).
     *
     * @param choices the {@link ChoiceEntry}s to search in
     * @param choice the choice to search
     * @return the found {@link ChoiceEntry} for the given choice or {@code null} otherwise
     */
    public static ChoiceEntry findChoice(List<ChoiceEntry> choices, String choice) {
        return choices.stream().filter(it -> it.getChoice().equals(choice)).findAny().orElse(null);
    }

    /**
     * Creates {@link ChoiceEntry}s for all given choices (Swing
     * {@code TacletOptionsSettings.createChoiceEntries}).
     *
     * @param choices the choices
     * @return the created {@link ChoiceEntry}s
     */
    public static List<ChoiceEntry> createChoiceEntries(Collection<String> choices) {
        if (choices == null) {
            return Collections.emptyList();
        }
        return choices.stream().map(TacletOptionsSettingsF::createChoiceEntry)
                .collect(Collectors.toList());
    }

    /**
     * Creates a {@link ChoiceEntry} for the given choice (Swing
     * {@code TacletOptionsSettings.createChoiceEntry}).
     *
     * @param choice the choice
     * @return the created {@link ChoiceEntry}
     */
    public static ChoiceEntry createChoiceEntry(String choice) {
        return new ChoiceEntry(choice, isUnsound(choice), isIncomplete(choice),
            getInformation(choice));
    }

    @Override
    public String getDescription() {
        return "Taclet Options";
    }

    @Override
    public Node getPanel(MainWindowF window) {
        loadedProof = window.getMediator().getSelectedProof();
        warnNoProof = loadedProof == null;
        setChoiceSettings(SettingsManagerF.getChoiceSettings(window));
        return this;
    }

    private void setChoiceSettings(ChoiceSettings choiceSettings) {
        category2Choice.clear();
        category2Choice.putAll(choiceSettings.getDefaultChoices());
        category2Choices.clear();
        category2Choices.putAll(choiceSettings.getChoices());
        rebuild();
    }

    /**
     * Rebuilds the warning headers and the collapsible category sections (Swing
     * {@code layoutChoiceSelector}/ {@code layoutHead}; the Swing original rebuilds on every
     * {@code getPanel} as well).
     */
    private void rebuild() {
        pCenter.getChildren().clear();
        addHeaderRows();
        category2Choice.keySet().stream().sorted(String::compareToIgnoreCase)
                .forEach(this::addCategory);
    }

    private void addHeaderRows() {
        Label noProofLoadedHeader =
            new Label("No Proof loaded. Taclet options may not be parsed.");
        noProofLoadedHeader.setGraphic(IconFactoryF.createIcon(Key.WARNING_INCOMPLETE));
        noProofLoadedHeader.getStyleClass().add("settings-warning-header");
        // Swing makes the header invisible when a proof is loaded
        noProofLoadedHeader.setVisible(warnNoProof);
        noProofLoadedHeader.setManaged(warnNoProof);
        addFullWidthRow(noProofLoadedHeader);

        Label lblHead2 = new Label("Taclet options will take effect only on new proofs.");
        lblHead2.setGraphic(IconFactoryF.createIcon(Key.WARNING_INCOMPLETE));
        lblHead2.getStyleClass().add("settings-warning-header");
        addFullWidthRow(lblHead2);
    }

    private void addFullWidthRow(Node node) {
        pCenter.add(node, 0, pCenter.getRowCount(), 3, 1);
    }

    private void addCategory(String cat) {
        List<ChoiceEntry> choices = createChoiceEntries(category2Choices.get(cat));
        ChoiceEntry selectedChoice = findChoice(choices, category2Choice.get(cat));
        String explanation = getExplanation(cat);

        Label title = createTitleRow(cat, selectedChoice);

        VBox selectPanel = new VBox(4);
        if (!warnNoProof) {
            // the Swing original shows the radio buttons only if a proof is loaded
            ToggleGroup btnGroup = new ToggleGroup();
            for (ChoiceEntry c : choices) {
                HBox row = mkRadioButton(c, btnGroup, title, cat);
                if (c.equals(selectedChoice)) {
                    ((RadioButton) row.getChildren().get(0)).setSelected(true);
                }
                selectPanel.getChildren().add(row);
            }
        }
        Label explanationArea = mkExplanation(explanation);
        VBox.setMargin(explanationArea, new Insets(0, 0, 0, 20));
        selectPanel.getChildren().add(explanationArea);

        // Swing collapses the sections by default (createCollapsableTitlePane)
        TitledPane catEntry = new TitledPane(null, selectPanel);
        catEntry.setGraphic(title);
        catEntry.setExpanded(false);
        addFullWidthRow(catEntry);
    }

    private Label mkExplanation(String explanation) {
        Label explanationArea = new Label(explanation.trim());
        explanationArea.setWrapText(true);
        explanationArea.getStyleClass().add("settings-explanation");
        return explanationArea;
    }

    /**
     * Creates the row of one radio button with its meta information icons (Swing
     * {@code mkRadioButton}): the choice marked with the incomplete/unsound icons and the extra
     * information as a help tooltip.
     */
    private HBox mkRadioButton(ChoiceEntry c, ToggleGroup btnGroup, Label title, String cat) {
        RadioButton button = new RadioButton(c.getChoice());
        button.setToggleGroup(btnGroup);
        HBox box = new HBox(6, button);
        box.setAlignment(Pos.CENTER_LEFT);

        if (c.isIncomplete()) {
            Label lbl = new Label(null, IconFactoryF.createIcon(Key.WARNING_INCOMPLETE));
            lbl.setTooltip(new Tooltip("Incomplete"));
            box.getChildren().add(lbl);
        }
        if (c.isUnsound()) {
            Label lbl = new Label(null, IconFactoryF.createIcon(Key.WARNING_UNSOUND));
            lbl.setTooltip(new Tooltip("Unsound"));
            box.getChildren().add(lbl);
        }
        if (c.getInformation() != null) {
            box.getChildren().add(SettingsPanelF.createHelpLabel(c.getInformation()));
        }

        // Swing ChoiceSettingsSetter: record the selection and update the section title
        button.setOnAction(e -> {
            category2Choice.put(cat, c.getChoice());
            title.setText(createCatTitleText(cat, c));
            checkForDifferingOptions(title, cat, c);
        });
        return box;
    }

    private Label createTitleRow(String cat, ChoiceEntry entry) {
        Label lbl = new Label(createCatTitleText(cat, entry));
        lbl.getStyleClass().add("settings-taclet-option-title");

        // we want to display a warning if the current choice differs from the loaded proof
        checkForDifferingOptions(lbl, cat, entry);

        return lbl;
    }

    private String createCatTitleText(String cat, ChoiceEntry entry) {
        // if no proof is loaded, we do not want to display current settings
        if (warnNoProof) {
            return cat;
        }

        // strip the leading "cat:" from "cat:value"
        return cat + (entry == null ? ""
                : " (set to '" + entry.getChoice().substring(cat.length() + 1) + "')");
    }

    /**
     * Checks if the current choice {@code entry} differs from the loaded proof and sets the
     * warning icon if necessary (Swing {@code checkForDifferingOptions}).
     *
     * @param lbl the label to set the icon on
     * @param cat the category of the choice
     * @param entry the current choice
     */
    private void checkForDifferingOptions(Label lbl, String cat, ChoiceEntry entry) {
        if (loadedProof != null) {
            String choiceOfLoadedProof =
                loadedProof.getSettings().getChoiceSettings().getDefaultChoices().get(cat);
            boolean choiceDiffers =
                entry != null && !entry.getChoice().equals(choiceOfLoadedProof);
            if (choiceDiffers) {
                lbl.setGraphic(IconFactoryF.createIcon(Key.WARNING_INCOMPLETE));
                // the Swing original places the icon behind the text (iconTextPosition LEFT)
                lbl.setContentDisplay(ContentDisplay.RIGHT);
                lbl.setTooltip(new Tooltip("The current choice of this option differs from the "
                    + "loaded proof.\nThe loaded proof uses: " + choiceOfLoadedProof));
            } else {
                lbl.setGraphic(null);
                lbl.setTooltip(null);
            }
        }
    }

    @Override
    public void apply(MainWindowF window) {
        // Apply to the global default choice settings - that is what (re)loading a problem reads
        // to build a new proof. When a proof is loaded, getChoiceSettings() hands this panel a
        // detached copy initialised from that proof (so it can show the proof's active options),
        // and writing the edited choices only into that copy silently dropped them: changing e.g.
        // the integer semantics and reloading kept the old taclet option. Write through to the
        // global settings. (Comment ported from the Swing original.)
        ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(category2Choice);
    }

    /**
     * Represents a choice with all its meta information (Swing
     * {@code TacletOptionsSettings.ChoiceEntry}).
     */
    public static class ChoiceEntry {

        /** text shown to the user in case of incompleteness */
        public static final String INCOMPLETE_TEXT = "incomplete";

        /** text shown to the user in case of unsoundness */
        public static final String UNSOUND_TEXT = "Java modeling unsound";

        private final String choice;
        private final boolean unsound;
        private final boolean incomplete;
        private final String information;

        /**
         * Constructor.
         *
         * @param choice the choice
         * @param unsound is unsound?
         * @param incomplete is incomplete?
         * @param information an optional information
         */
        public ChoiceEntry(String choice, boolean unsound, boolean incomplete,
                String information) {
            this.choice = choice;
            this.unsound = unsound;
            this.incomplete = incomplete;
            this.information = information;
        }

        /** @return the choice */
        public String getChoice() {
            return choice;
        }

        /**
         * Checks for soundness.
         *
         * @return {@code true} unsound, {@code false} sound
         */
        public boolean isUnsound() {
            return unsound;
        }

        /**
         * Checks for completeness.
         *
         * @return {@code true} incomplete, {@code false} complete
         */
        public boolean isIncomplete() {
            return incomplete;
        }

        /** @return the optionally available information */
        public String getInformation() {
            return information;
        }

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

        @Override
        public boolean equals(Object obj) {
            if (obj instanceof ChoiceEntry other) {
                return choice.equals(other.getChoice()) && incomplete == other.isIncomplete()
                        && unsound == other.isUnsound()
                        && java.util.Objects.equals(information, other.getInformation());
            }
            return false;
        }

        @Override
        public String toString() {
            if (unsound && incomplete) {
                if (information != null) {
                    return String.format("%s (%s and %s, %s)", choice, UNSOUND_TEXT,
                        INCOMPLETE_TEXT, information);
                }
                return String.format("%s (%s and %s)", choice, UNSOUND_TEXT, INCOMPLETE_TEXT);
            } else if (unsound) {
                if (information != null) {
                    return String.format("%s (%s, %s)", choice, UNSOUND_TEXT, information);
                }
                return String.format("%s (%s)", choice, UNSOUND_TEXT);
            } else if (incomplete) {
                if (information != null) {
                    return String.format("%s (%s, %s)", choice, INCOMPLETE_TEXT, information);
                }
                return String.format("%s (%s)", choice, INCOMPLETE_TEXT);
            }
            if (information != null) {
                return String.format("%s (%s)", choice, information);
            }
            return choice;
        }
    }
}
