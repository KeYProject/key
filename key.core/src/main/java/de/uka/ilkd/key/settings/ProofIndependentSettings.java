/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.beans.PropertyChangeListener;
import java.io.*;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.pp.NotationInfo;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Top of the proof independent settings.
 * <p>
 * You can add your own settings by calling {@link #addSettings(Settings)}.
 *
 * @see Settings
 */
public class ProofIndependentSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofIndependentSettings.class);

    public static final ProofIndependentSettings DEFAULT_INSTANCE;

    static {
        var file = new File(PathConfig.getProofIndependentSettings().replace(".props", ".json"));
        if (file.exists()) {
            DEFAULT_INSTANCE = new ProofIndependentSettings(file);
        } else {
            var old = new File(PathConfig.getProofIndependentSettings());
            DEFAULT_INSTANCE = new ProofIndependentSettings(old);
        }
    }

    private final ProofIndependentSMTSettings smtSettings =
        ProofIndependentSMTSettings.getDefaultSettingsData();

    private final LemmaGeneratorSettings lemmaGeneratorSettings = new LemmaGeneratorSettings();
    private final GeneralSettings generalSettings = new GeneralSettings();
    private final ViewSettings viewSettings = new ViewSettings();
    private final TermLabelSettings termLabelSettings = new TermLabelSettings();
    private final FeatureSettings featureSettings = new FeatureSettings();

    private File filename;


    private final List<Settings> settings = new LinkedList<>();

    private final PropertyChangeListener settingsListener = e -> saveSettings();
    private Properties lastReadedProperties;
    private Configuration lastReadedConfiguration;

    private ProofIndependentSettings() {
        addSettings(smtSettings);
        addSettings(lemmaGeneratorSettings);
        addSettings(generalSettings);
        addSettings(viewSettings);
        addSettings(featureSettings);
    }

    private ProofIndependentSettings(File filename) {
        this();
        this.filename = filename;
        loadSettings();
    }

    public void addSettings(Settings settings) {
        if (!this.settings.contains(settings)) {
            this.settings.add(settings);
            settings.addPropertyChangeListener(settingsListener);
            if (lastReadedProperties != null) {
                settings.readSettings(lastReadedProperties);
            }
            if (lastReadedConfiguration != null) {
                settings.readSettings(lastReadedConfiguration);
            }
        }
    }

    private void loadSettings() {
        try {
            if (filename.exists()) {
                if (Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY)) {
                    LOGGER.warn("The settings in {} are *not* read due to flag '{}'", filename,
                        PathConfig.DISREGARD_SETTINGS_PROPERTY);
                } else {
                    load(filename);
                }
            }
        } catch (IOException e) {
            LOGGER.error("Could not load settings from {}", filename, e);
        }
    }

    private void load(File file) throws IOException {
        if (!file.getName().endsWith(".json")) {
            try (FileInputStream in = new FileInputStream(file)) {
                Properties properties = new Properties();
                properties.load(in);
                for (Settings settings : settings) {
                    settings.readSettings(properties);
                }
                lastReadedProperties = properties;
            }
        } else {
            this.lastReadedConfiguration = Configuration.load(file);
            for (Settings settings : settings) {
                settings.readSettings(lastReadedConfiguration);
            }
        }
    }

    public void saveSettings() {
        if (!filename.getName().endsWith(".json")) {
            Properties result = new Properties();
            for (Settings settings : settings) {
                settings.writeSettings(result);
            }

            if (!filename.exists()) {
                filename.getParentFile().mkdirs();
            }

            try (var out = new FileOutputStream(filename)) {
                result.store(out, "Proof-Independent-Settings-File. Generated " + new Date());
            } catch (IOException e) {
                LOGGER.error("Could not store settings to {}", filename, e);
            }
        }

        Configuration config = new Configuration();
        for (var settings : settings)
            settings.writeSettings(config);
        if (!filename.exists()) {
            filename.getParentFile().mkdirs();
        }

        try (var out =
            new BufferedWriter(new FileWriter(filename.toString().replace(".props", ".json")))) {
            config.save(out, "Proof-Independent-Settings-File. Generated " + new Date());
        } catch (IOException e) {
            LOGGER.error("Could not store settings to {}", filename, e);
        }
    }

    public GeneralSettings getGeneralSettings() {
        return generalSettings;
    }

    public TermLabelSettings getTermLabelSettings() {
        return termLabelSettings;
    }

    public ViewSettings getViewSettings() {
        return viewSettings;
    }

    public LemmaGeneratorSettings getLemmaGeneratorSettings() {
        return lemmaGeneratorSettings;
    }

    public ProofIndependentSMTSettings getSMTSettings() {
        return smtSettings;
    }

    public FeatureSettings getFeatureSettings() {
        return featureSettings;
    }

    /**
     * Checks if pretty printing is enabled or not.
     *
     * @return {@code true} pretty printing is enabled, {@code false} pretty printing is disabled.
     */
    public static boolean isUsePrettyPrinting() {
        return ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
    }

    /**
     * Defines if pretty printing is enabled or not.
     *
     * @param usePrettyPrinting {@code true} pretty printing is enabled, {@code false} pretty
     *        printing is disabled.
     */
    public static void setUsePrettyPrinting(boolean usePrettyPrinting) {
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUsePretty(usePrettyPrinting);
        NotationInfo.DEFAULT_PRETTY_SYNTAX = usePrettyPrinting;
    }
}
