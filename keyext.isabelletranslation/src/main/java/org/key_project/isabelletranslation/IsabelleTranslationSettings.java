/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.isabelletranslation;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Objects;
import java.util.Properties;
import java.util.stream.Collectors;

import de.uka.ilkd.key.settings.AbstractSettings;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Settings object used for Isabelle translation.
 */
public class IsabelleTranslationSettings extends AbstractSettings {
    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslationSettings.class);

    /**
     * the file where settings are stored
     */
    protected static final File SETTINGS_FILE_NEW =
        new File(PathConfig.getKeyConfigDir(), "isabelleSettings.json");
    /**
     * The settings instance
     */
    private static IsabelleTranslationSettings INSTANCE;

    /**
     * Key to get Isabelle path in JSON
     */
    protected static final String isabellePathKey = "Path";
    /**
     * Key to get translation path in JSON
     */
    protected static final String translationPathKey = "TranslationPath";
    /**
     * Key to get timeout in JSON
     */
    protected static final String timeoutKey = "Timeout";

    /**
     * The Isabelle path
     */
    private Path isabellePath;
    /**
     * The translation path
     */
    private Path translationPath;
    /**
     * The timeout in seconds
     */
    private int timeoutSeconds;

    /**
     * The default path for Isabelle
     */
    private static final Path DEFAULT_ISABELLE_PATH =
        Path.of(System.getProperty("user.home"), "Isabelle2024-RC1");
    /**
     * The default path for translations
     */
    private static final Path DEFAULT_TRANSLATION_PATH =
        Path.of(PathConfig.getKeyConfigDir(), "IsabelleTranslations");
    /**
     * default timeout setting
     */
    private static final int DEFAULT_TIMEOUT_SECONDS = 30;


    private static Configuration getDefaultConfig() {
        Configuration config = new Configuration();
        config.set(isabellePathKey, DEFAULT_ISABELLE_PATH);
        config.set(translationPathKey, DEFAULT_TRANSLATION_PATH);
        config.set(timeoutKey, DEFAULT_TIMEOUT_SECONDS);
        return config;
    }

    private IsabelleTranslationSettings(Configuration load) {
        readSettings(load);
        Runtime.getRuntime().addShutdownHook(new Thread(this::save));
    }

    /**
     * Returns the instance of this class
     *
     * @return instance of this class
     */
    public static IsabelleTranslationSettings getInstance() {
        if (INSTANCE == null) {
            if (SETTINGS_FILE_NEW.exists()) {
                try {
                    LOGGER.info("Load Isabelle settings at {}", SETTINGS_FILE_NEW);
                    return INSTANCE =
                        new IsabelleTranslationSettings(Configuration.load(SETTINGS_FILE_NEW));
                } catch (IOException e) {
                    LOGGER.error("Could not read {}, resorting to default settings",
                        SETTINGS_FILE_NEW, e);
                    return INSTANCE = new IsabelleTranslationSettings(getDefaultConfig());
                }
            }
            LOGGER.info("No settings present, resorting to default Isabelle settings");
            return INSTANCE = new IsabelleTranslationSettings(getDefaultConfig());
        }
        return INSTANCE;
    }

    protected void createSessionFiles() {
        Path sessionRootPath = Path.of(translationPath + "/ROOT");
        BufferedReader sessionReader = new BufferedReader(
            new InputStreamReader(Objects.requireNonNull(getClass().getResourceAsStream("ROOT"))));
        String sessionRoot =
            sessionReader.lines().collect(Collectors.joining(System.lineSeparator()));

        Path sessionDocumentPath = Path.of(translationPath + "/document/root.tex");
        BufferedReader sessionDocumentReader = new BufferedReader(new InputStreamReader(
            Objects.requireNonNull(getClass().getResourceAsStream("root.tex"))));
        String sessionDocument =
            sessionDocumentReader.lines().collect(Collectors.joining(System.lineSeparator()));

        try {
            Files.createDirectories(sessionDocumentPath.getParent());
            Files.write(sessionRootPath, sessionRoot.getBytes());
            Files.write(sessionDocumentPath, sessionDocument.getBytes());
            LOGGER.info("Created Isabelle session files at: {}", translationPath);
        } catch (IOException e) {
            LOGGER.error("Failed to create ROOT file for Isabelle Translation, because: {}",
                e.toString());
        }
    }

    /**
     * Writes the settings to the JSON file
     */
    public void save() {
        LOGGER.info("Save Isabelle settings to: {}", SETTINGS_FILE_NEW.getAbsolutePath());
        try (Writer writer = new FileWriter(SETTINGS_FILE_NEW)) {
            var config = new Configuration();
            writeSettings(config);
            config.save(writer, "Isabelle settings");
            writer.flush();
        } catch (IOException ex) {
            LOGGER.error("Failed to save Isabelle settings", ex);
        }
    }

    @Override
    public void readSettings(Properties props) {
        isabellePath = Path.of(props.getProperty(isabellePathKey));
        Path newTranslationPath = Path.of(props.getProperty(translationPathKey));
        if (newTranslationPath != translationPath) {
            translationPath = newTranslationPath;
            createSessionFiles();
        }
        timeoutSeconds = Integer.parseInt(props.getProperty(timeoutKey, "30"));
    }

    @Override
    public void writeSettings(Properties props) {
        props.setProperty(isabellePathKey, isabellePath.toString());
        props.setProperty(translationPathKey, translationPath.toString());
        props.setProperty(timeoutKey, String.valueOf(timeoutSeconds));
    }

    @Override
    public void readSettings(@NonNull Configuration props) {
        if (isabellePath == null || translationPath == null) {
            isabellePath = DEFAULT_ISABELLE_PATH;
            translationPath = DEFAULT_TRANSLATION_PATH;
        }
        isabellePath = Path.of(props.getString(isabellePathKey, isabellePath.toString()));

        Path newTranslationPath =
            Path.of(props.getString(translationPathKey, translationPath.toString()));
        if (newTranslationPath != translationPath) {
            translationPath = newTranslationPath;
            createSessionFiles();
        }

        timeoutSeconds = props.getInt(timeoutKey, 30);
    }

    @Override
    public void writeSettings(@NonNull Configuration props) {
        props.set(isabellePathKey, isabellePath.toString());
        props.set(translationPathKey, translationPath.toString());
        props.set(timeoutKey, String.valueOf(timeoutSeconds));
    }

    /**
     * @return
     *         The header used for translation theories. Includes the preamble and Main theory
     *         imports
     */
    public String getHeader() {
        return "theory Translation imports Main KeYTranslations.TranslationPreamble begin";
    }

    public Path getIsabellePath() {
        return isabellePath;
    }

    public Path getTranslationPath() {
        return translationPath;
    }

    public int getTimeout() {
        return this.timeoutSeconds;
    }

    public void setTimeout(int i) {
        timeoutSeconds = i;
    }
}
