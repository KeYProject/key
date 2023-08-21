/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.beans.PropertyChangeListener;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
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

    public static final ProofIndependentSettings DEFAULT_INSTANCE =
        new ProofIndependentSettings(PathConfig.getProofIndependentSettings());

    private final ProofIndependentSMTSettings smtSettings =
        ProofIndependentSMTSettings.getDefaultSettingsData();

    private final LemmaGeneratorSettings lemmaGeneratorSettings = new LemmaGeneratorSettings();
    private final GeneralSettings generalSettings = new GeneralSettings();
    private final ViewSettings viewSettings = new ViewSettings();
    private final TermLabelSettings termLabelSettings = new TermLabelSettings();
    private final String filename;


    private final List<Settings> settings = new LinkedList<>();

    private final PropertyChangeListener settingsListener = e -> saveSettings();
    private Properties lastReadedProperties;

    private ProofIndependentSettings(String filename) {
        addSettings(smtSettings);
        addSettings(lemmaGeneratorSettings);
        addSettings(generalSettings);
        addSettings(viewSettings);
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
        }
    }

    private void loadSettings() {
        try {
            File testFile = new File(filename);
            if (testFile.exists()) {
                if (Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY)) {
                    LOGGER.warn("The settings in {} are *not* read due to flag '{}'", filename,
                        PathConfig.DISREGARD_SETTINGS_PROPERTY);
                } else {
                    load(testFile);
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private void load(File file) throws IOException {
        try (FileInputStream in = new FileInputStream(file)) {
            Properties properties = new Properties();
            properties.load(in);
            for (Settings settings : settings) {
                settings.readSettings(properties);
            }
            lastReadedProperties = properties;
        }
    }

    public void saveSettings() {
        Properties result = new Properties();
        for (Settings settings : settings) {
            settings.writeSettings(result);
        }

        File file = new File(filename);
        if (!file.exists()) {
            file.getParentFile().mkdirs();
        }

        try (FileOutputStream out = new FileOutputStream(file)) {
            result.store(out, "Proof-Independent-Settings-File. Generated " + new Date());
        } catch (IOException e) {
            throw new RuntimeException(e);
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
