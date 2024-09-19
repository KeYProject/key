/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof;

import java.io.File;
import java.io.IOException;
import java.util.*;

public class ProofCollectionSettings {
    /*
     * Known constants for entries that may occur in field settingsMap.
     */
    private static final String BASE_DIRECTORY_KEY = "baseDirectory";
    private static final String KEY_SETTINGS_KEY = "keySettings";
    private static final String LOCAL_SETTINGS_KEY = "localSettings";
    private static final String STATISTICS_FILE = "statisticsFile";
    private static final String RELOAD_ENABLED = "reloadEnabled";
    private static final String TEMP_DIR = "tempDir";
    private static final String RUN_ONLY_ON = "runOnlyOn";
    private static final String DIRECTORY = "directory";

    public static final String VERBOSE_OUTPUT_KEY = "verboseOutput";
    public static final String IGNORE_KEY = "ignore";

    /**
     * The time at which the corresponding runallproofs run has been started.
     */
    public final Date runStart;

    /**
     * String {@link Map} containing all settings entries.
     */
    private final Map<String, String> settingsMap;

    /**
     * File in which statistics are written.
     */
    private StatisticsFile statisticsFile;

    /**
     * In order to ensure that the implementation is independent of working directory, this method
     * can be used to return an absolute {@link File} object.
     *
     * @param baseDirectory Base directory that will be used as start location in case given path
     *        name is a relative path.
     * @param pathName Path whose associated {@link File} object will be returned.
     * @return {@link File} object pointing to given path name relative to given base directory.
     */
    static File getAbsoluteFile(File baseDirectory, String pathName) {

        /*
         * Caller of this method must provide an absolute path as base directory.
         */
        if (!baseDirectory.isAbsolute()) {
            throw new RuntimeException("Expecting an absolute path but found: " + baseDirectory);
        }

        if (!baseDirectory.isDirectory()) {
            throw new RuntimeException(
                "Given file system location is not a directory: " + baseDirectory);
        }

        /*
         * Initial directory is ignored in case provided path name is absolute.
         */
        File tmp = new File(pathName);
        File ret = tmp.isAbsolute() ? tmp : new File(baseDirectory, pathName);

        /*
         * Resulting file object should be absolute. This is just a safety check.
         */
        assert ret.isAbsolute() : "Expecting an absolute path but found: " + ret;

        return ret;
    }

    /**
     * Creates a {@link ProofCollectionSettings} object from the specified
     * parameters with no parent
     * settings.
     */
    public ProofCollectionSettings(Date runStart) {
        this.runStart = runStart;
        settingsMap = new LinkedHashMap<>();
    }

    /**
     * Creates a {@link ProofCollectionSettings} object that overrides an existing
     * {@link ProofCollectionSettings} object.
     */
    public ProofCollectionSettings(ProofCollectionSettings parentSettings) {
        this.runStart = parentSettings.runStart;
        settingsMap = new HashMap<>(parentSettings.settingsMap);

        /*
         * Inherit statistics file from parent settings.
         */
        statisticsFile = parentSettings.getStatisticsFile();
    }

    /**
     * Reads out generic settings, which were be specified as (key, value) pairs
     * during object
     * creation.
     *
     * @see Map.Entry
     */
    private String get(String key) {
        return settingsMap.get(key);
    }

    private ProofCollectionSettings set(String key, String value) {
        settingsMap.put(key, value);
        return this;
    }

    /**
     * Settings must specify a base directory. Relative
     * {@link ProofCollectionSettings} paths will
     * be treated as relative to directory returned by this method.
     */
    public File getBaseDirectory() {
        String baseDirectoryName = get(BASE_DIRECTORY_KEY);
        return baseDirectoryName == null
                ? new File(".").getAbsoluteFile()
                : new File(baseDirectoryName).getAbsoluteFile();
    }

    /**
     * Returns location of statistics file. Can be null. In this case no statistics
     * are saved.
     */
    public StatisticsFile getStatisticsFile() {
        if (statisticsFile == null) {
            // Compute location of statistics file.
            String statisticsFileName = get(STATISTICS_FILE);
            if (statisticsFileName == null) {
                statisticsFile = null;
            } else {
                statisticsFile =
                    new StatisticsFile(getAbsoluteFile(getBaseDirectory(), statisticsFileName));
            }
        }
        return statisticsFile;
    }

    public File getTempDir() throws IOException {
        String tempDirString = get(TEMP_DIR);
        if (tempDirString == null) {
            throw new IOException(
                "No temporary directory specified in RunAllProofs configuration file. "
                    + "Cannot run in forked mode. " + "To solve this, specify setting \"" + TEMP_DIR
                    + "\" in file ");
        }
        File tempDir = new File(tempDirString);
        if (!tempDir.isAbsolute()) {
            tempDir = new File(getBaseDirectory(), tempDirString);
        }
        if (tempDir.isFile()) {
            throw new IOException("Specified temporary directory is a file: " + tempDir + "\n"
                + "Configure temporary directory in file to solve this.");
        }
        return tempDir;
    }

    /**
     * Check whether proof reloading is enabled or disabled. If enabled, closed
     * proofs will be saved
     * and reloaded after prover is finished.
     */
    public boolean reloadEnabled() {
        String reloadEnabled = get(RELOAD_ENABLED);
        if (reloadEnabled == null || reloadEnabled.equals("true") || reloadEnabled.isEmpty()) {
            return true;
        } else if (reloadEnabled.equals("false")) {
            return false;
        } else {
            return true;
        }
    }

    /**
     * Gets the list of groups on which the test should be run.
     *
     * <code>null</code> means all of them, otherwise a list of group names
     *
     * @return <code>null</code> or a list.
     */
    public List<String> getRunOnlyOn() {
        String runOnly = get(RUN_ONLY_ON);
        if (runOnly == null) {
            return null;
        } else {
            return Arrays.asList(runOnly.trim().split(" *, *"));
        }
    }

    /**
     * Gets the directory for a group.
     * <p>
     * If the groups has its own directory key, take it into consideration, return
     * the base
     * directory otherwise
     *
     * @return the directory for the current group.
     */
    public File getGroupDirectory() {
        String localDir = get(DIRECTORY);
        if (localDir != null) {
            return new File(getBaseDirectory(), localDir);
        } else {
            return getBaseDirectory();
        }
    }

    public ProofCollectionSettings setBaseDirectory(String folder) {
        return set(BASE_DIRECTORY_KEY, folder);
    }

    public ProofCollectionSettings setStatisticsFile(String path) {
        return set(STATISTICS_FILE, path);
    }

    public ProofCollectionSettings setReloadEnabled(boolean flag) {
        return set(RELOAD_ENABLED, "" + flag);
    }

    public ProofCollectionSettings setTempDir(String path) {
        return set(TEMP_DIR, path);
    }

    public ProofCollectionSettings setKeySettings(String props) {
        return set(KEY_SETTINGS_KEY, props);
    }

    public ProofCollectionSettings setLocalKeYSettings(String settings) {
        return set(LOCAL_SETTINGS_KEY, settings);
    }

    public ProofCollectionSettings setRunOnlyOn(String settings) {
        return set(RUN_ONLY_ON, settings);
    }

    public boolean getVerboseOutput() {
        return "true".equals(get(VERBOSE_OUTPUT_KEY));
    }

    public ProofCollectionSettings setVerboseOutput(boolean val) {
        return set(VERBOSE_OUTPUT_KEY, "" + val);
    }

    public boolean getIgnoreTest() {
        return "true".equals(get(IGNORE_KEY));
    }

    public ProofCollectionSettings setDirectory(String s) {
        return set(DIRECTORY, s);
    }
}
