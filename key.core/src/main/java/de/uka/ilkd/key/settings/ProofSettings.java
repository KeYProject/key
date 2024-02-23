/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.beans.PropertyChangeListener;
import java.io.*;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.*;

import de.uka.ilkd.key.util.KeYResourceManager;

import org.antlr.v4.runtime.CharStreams;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class is used to load and save settings for proofs such as which data type models are used
 * to represent the java types. Which heuristics have to be loaded and so on. The class loads the
 * file proofsettings.config from the place where you started key. If the file is not available
 * standard settings are used. The loaded file has the following structure: <code>
 * // KeY-Configuration file
 * ActiveHeuristics=simplify_prog , simplify
 * MaximumNumberOfHeuristcsApplications=400
 * number  = IntegerLDT.class
 * boolean = BooleanLDT.class
 * </code>
 *
 * @see Properties
 * @see Settings
 */
@NullMarked
public class ProofSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSettings.class);

    public static final File PROVER_CONFIG_FILE =
        new File(PathConfig.getKeyConfigDir(), "proof-settings.props");

    public static final File PROVER_CONFIG_FILE_NEW =
        new File(PathConfig.getKeyConfigDir(), "proof-settings.json");

    public static final URL PROVER_CONFIG_FILE_TEMPLATE = KeYResourceManager.getManager()
            .getResourceFile(ProofSettings.class, "default-proof-settings.json");

    public static final ProofSettings DEFAULT_SETTINGS = ProofSettings.loadedSettings();
    public static final String KEY_ADDITIONAL_DATA = "additionalInformation";


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

    private @Nullable Properties lastLoadedProperties = null;
    private @Nullable Configuration lastLoadedConfiguration = null;

    /**
     * create a proof settings object. When you add a new settings object, PLEASE UPDATE THE LIST
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
     * copy constructor - substitutes .clone() in classes implementing Settings
     */
    public ProofSettings(ProofSettings toCopy) {
        this();
        Properties result = new Properties();
        lastLoadedProperties = toCopy.lastLoadedProperties;
        for (Settings s : toCopy.settings) {
            s.writeSettings(result);
        }
        for (Settings s : settings) {
            s.readSettings(result);
        }
    }


    public void addSettings(Settings settings) {
        this.settings.add(settings);
        settings.addPropertyChangeListener(listener);
        if (lastLoadedProperties != null) {
            settings.readSettings(lastLoadedProperties);
        }
        if (lastLoadedConfiguration != null) {
            settings.readSettings(lastLoadedConfiguration);
        }
    }

    /**
     * @deprecated {@link #getConfiguration}
     */
    @Deprecated
    public Properties getProperties() {
        Properties result = new Properties();
        for (Settings s : settings) {
            s.writeSettings(result);
        }
        return result;
    }

    public Configuration getConfiguration() {
        var config = new Configuration();
        for (Settings s : settings) {
            s.writeSettings(config);
        }
        return config;
    }

    /**
     * Write the settings to the given stream w/o additional information.
     *
     * @see #settingsToStream(Writer, Map)
     */
    public void settingsToStream(Writer out) {
        settingsToStream(out, null);
    }

    /**
     * Writes the settings to the given stream storing additional data into
     * {@link #KEY_ADDITIONAL_DATA}.
     *
     * @param out a output destination
     * @param additionalInformation a nullable map of additional information
     */
    public void settingsToStream(Writer out, @Nullable Map<String, Object> additionalInformation) {
        var config = getConfiguration();
        if (additionalInformation != null) {
            config.set(KEY_ADDITIONAL_DATA, new Configuration(additionalInformation));
        }
        config.save(out, "Proof-Settings-Config-File");
    }

    /**
     * Saves the current settings in this dialog into a configuration file.
     */
    public void saveSettings() {
        try {
            if (!PROVER_CONFIG_FILE_NEW.exists()) {
                PROVER_CONFIG_FILE.getParentFile().mkdirs();
            }
            try (Writer out = new BufferedWriter(
                new FileWriter(PROVER_CONFIG_FILE_NEW, StandardCharsets.UTF_8))) {
                settingsToStream(out);
            }
        } catch (IOException e) {
            LOGGER.warn("Could not save proof-settings.", e);
        }
    }

    public String settingsToString() {
        return settingsToString(new HashMap<>());
    }

    public String settingsToString(Map<String, Object> additionalInformation) {
        StringWriter out = new StringWriter();
        settingsToStream(out, additionalInformation);
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
     * Used by loadSettings() and loadSettingsFromString(...)
     *
     * @deprecated in favour of {@link #loadSettingsFromJSONStream(Reader)}
     */
    @Deprecated
    public void loadSettingsFromPropertyStream(Reader in) {
        Properties props = new Properties();
        try {
            props.load(in);
        } catch (IOException e) {
            LOGGER.warn("Error on loading proof-settings.", e);
        }
        lastLoadedProperties = props;
        lastLoadedConfiguration = null;
        for (Settings s : settings) {
            s.readSettings(props);
        }
    }

    /**
     * Loads the former settings from configuration file.
     */
    public void loadSettings() {
        if (Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY)) {
            LOGGER.warn("The settings in {} are *not* read.", PROVER_CONFIG_FILE);
        } else {
            var isOldFormat = !PROVER_CONFIG_FILE_NEW.exists();
            var fileToUse = isOldFormat ? PROVER_CONFIG_FILE : PROVER_CONFIG_FILE_NEW;
            try (var in = new BufferedReader(new FileReader(fileToUse, StandardCharsets.UTF_8))) {
                LOGGER.info("Load proof dependent settings from file {}", fileToUse);
                if (isOldFormat) {
                    loadDefaultJSONSettings();
                    loadSettingsFromPropertyStream(in);
                } else {
                    loadDefaultJSONSettings();
                    loadSettingsFromJSONStream(in);
                }
            } catch (IOException e) {
                LOGGER.warn("No proof-settings could be loaded, using defaults", e);
            }
        }
    }


    /**
     * Used to load Settings from a .key file
     */
    public void loadSettingsFromPropertyString(String s) {
        if (s == null) {
            return;
        }
        StringReader reader = new StringReader(s);
        loadSettingsFromPropertyStream(reader);
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
        return !ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getChoices().isEmpty();
    }

    /**
     * Update the proof settings according to the entries on the properties.
     *
     * @param props a non-<code>null</code> object with KeY properties.
     */
    public void update(Properties props) {
        for (Settings s : settings) {
            s.readSettings(props);
        }
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
        lastLoadedProperties = null;
        lastLoadedConfiguration = c;
        for (Settings setting : settings)
            setting.readSettings(c);
    }
}
