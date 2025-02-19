/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import de.uka.ilkd.key.util.KeYResourceManager;
import org.antlr.v4.runtime.CharStreams;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.beans.PropertyChangeListener;
import java.io.*;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

/// This class is used to load and save settings for proofs such as which data type models are used
/// to represent the java types.
/// Which heuristics have to be loaded and so on?
/// The class loads the file `proofsettings.config` from the place where you started key.
/// If the file is not available, standard settings are used.
/// The loaded file has the following structure:
///
/// ```
/// // KeY-Configuration file
/// ActiveHeuristics=["simplify_prog", "simplify"]
/// MaximumNumberOfHeuristcsApplications=400
/// number = "IntegerLDT.class"
/// boolean = "BooleanLDT.class"
///```
///
/// @see Properties
/// @see Settings
public class ProofSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSettings.class);

    public static final File PROVER_CONFIG_FILE =
            new File(PathConfig.getKeyConfigDir(), "proof-settings.json");

    public static final URL PROVER_CONFIG_FILE_TEMPLATE = KeYResourceManager.getManager()
            .getResourceFile(ProofSettings.class, "default-proof-settings.json");

    public static final ProofSettings DEFAULT_SETTINGS = loadedSettings();


    private static ProofSettings loadedSettings() {
        ProofSettings ps = new ProofSettings();
        ps.loadSettings();
        return ps;
    }

    /**
     * all setting objects in the following order: heuristicSettings
     */
    private final List<Settings> settings = new LinkedList<>();

    /**
     * the default listener to settings
     */
    private final PropertyChangeListener listener = e -> saveSettings();

    private final StrategySettings strategySettings = new StrategySettings();
    private final ChoiceSettings choiceSettings = new ChoiceSettings();
    private final ProofDependentSMTSettings smtSettings =
            ProofDependentSMTSettings.getDefaultSettingsData();
    private final NewSMTTranslationSettings newSMTSettings = new NewSMTTranslationSettings();
    private final TermLabelSettings termLabelSettings = new TermLabelSettings();

    private Configuration lastLoadedConfiguration = null;

    /**
     * Create a proof settings object. When you add a new settings object, PLEASE UPDATE THE LIST
     * ABOVE AND USE THOSE CONSTANTS INSTEAD OF USING INTEGERS DIRECTLY
     */
    private ProofSettings() {
        addSettings(strategySettings);
        addSettings(choiceSettings);
        addSettings(smtSettings);
        addSettings(termLabelSettings);
        addSettings(newSMTSettings);
    }

    /*
     * copy constructor - substitutes .copy() in classes implementing Settings
     */
    public ProofSettings(ProofSettings toCopy) {
        this();
        lastLoadedConfiguration = toCopy.lastLoadedConfiguration;
        Configuration result = toCopy.asConfiguration();
        for (Settings s : settings) {
            s.readSettings(result);
        }
    }

    public Configuration asConfiguration() {
        Configuration result = new Configuration();
        for (Settings s : settings) {
            s.writeSettings(result);
        }
        return result;
    }


    public void addSettings(Settings settings) {
        this.settings.add(settings);
        settings.addPropertyChangeListener(listener);
        if (lastLoadedConfiguration != null) {
            settings.readSettings(lastLoadedConfiguration);
        }
    }

    /**
     * Serializes the current hierarchy of settings into a {@link Configuration} object which
     * represents
     * a tree of {@link java.util.Map}s.
     *
     * @return the current configuration in form of a {@link Configuration} object.
     */
    public Configuration getConfiguration() {
        var config = new Configuration();
        for (Settings s : settings) {
            s.writeSettings(config);
        }
        return config;
    }

    /**
     * Used by saveSettings() and settingsToString()
     */
    public void settingsToStream(Writer out) {
        getConfiguration().save(out, "Proof-Settings-Config-File");
    }

    /**
     * Saves the current settings in this dialog into a configuration file.
     */
    public void saveSettings() {
        try {
            if (PROVER_CONFIG_FILE.getParentFile().mkdirs()) {
                try (Writer out = new BufferedWriter(
                        new FileWriter(PROVER_CONFIG_FILE, StandardCharsets.UTF_8))) {
                    settingsToStream(out);
                }
            }
        } catch (IOException e) {
            LOGGER.warn("Could not save proof-settings.", e);
        }
    }

    public String settingsToString() {
        StringWriter out = new StringWriter();
        settingsToStream(out);
        return out.getBuffer().toString();
    }

    public void loadSettingsFromJSONStream(Reader in) throws IOException {
        var config = Configuration.load(CharStreams.fromReader(in));
        readSettings(config);
    }

    public void loadDefaultJSONSettings() {
        if (PROVER_CONFIG_FILE_TEMPLATE == null) {
            LOGGER.warn(
                    "default proof-settings file 'default-proof-settings.json' could not be found.");
        } else {
            try (var in = new InputStreamReader(PROVER_CONFIG_FILE_TEMPLATE.openStream())) {
                loadSettingsFromJSONStream(in);
            } catch (IOException e) {
                LOGGER.error("Default proof-settings could not be loaded.", e);
            }
        }
    }

    /**
     * Loads the former settings from a configuration file.
     */
    public void loadSettings() {
        if (Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY)) {
            LOGGER.warn("The settings in {} are *not* read.", PROVER_CONFIG_FILE);
        } else {
            var fileToUse = PROVER_CONFIG_FILE;
            try (var in = new BufferedReader(new FileReader(fileToUse, StandardCharsets.UTF_8))) {
                LOGGER.info("Load proof dependent settings from file {}", fileToUse);
                loadDefaultJSONSettings();
                loadSettingsFromJSONStream(in);
            } catch (IOException e) {
                LOGGER.warn("No proof-settings could be loaded, using defaults", e);
            }
        }
    }

    /**
     * returns the StrategySettings object
     *
     * @return the StrategySettings object
     */
    public StrategySettings getStrategySettings() {
        return strategySettings;
    }

    /**
     * returns the ChoiceSettings object
     *
     * @return the ChoiceSettings object
     */
    public ChoiceSettings getChoiceSettings() {
        return choiceSettings;
    }

    /**
     * returns the DecisionProcedureSettings object
     *
     * @return the DecisionProcedureSettings object
     */
    public ProofDependentSMTSettings getSMTSettings() {
        return smtSettings;
    }

    public NewSMTTranslationSettings getNewSMTSettings() {
        return newSMTSettings;
    }

    /**
     * Checks if the choice settings are initialized.
     *
     * @return {@code true} settings are initialized, {@code false} settings are not initialized.
     */
    public static boolean isChoiceSettingInitialised() {
        return !DEFAULT_SETTINGS.getChoiceSettings().getChoices().isEmpty();
    }

    /**
     * Returns the term label settings from the proof settings.
     *
     * @return the term label settings
     */
    public TermLabelSettings getTermLabelSettings() {
        return termLabelSettings;
    }

    public void readSettings(Configuration c) {
        lastLoadedConfiguration = c;
        for (Settings setting : settings)
            setting.readSettings(c);
    }
}
