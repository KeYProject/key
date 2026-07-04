/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.settings;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Objects;
import java.util.stream.Stream;

import de.uka.ilkd.key.util.KeYResourceManager;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/// This class contains the pahts where the core of KeY looks for certain files and directories.
///
/// By default, all KeY configurations are stored in a directory named `.key` inside the user's home
/// directory, determined by the system property `System.getProperty("user.home")`.
/// This points `$HOME` (linux/unix/macos) or Microsoft Windows `%USERPROFILE%`.
///
/// This path can be manipulated by using `key.home`. Since KeY version 3.0, the configuration
/// itself
/// lives now in a sub-directory of `key.home`. This
///
/// | System property | Explanation | Default | |
/// |-------------|-------------|---------|-----|
/// | key.home | base path to the configurations | `user.home/.key` |
/// | key.config | path to the configuration | `key.home/3.0` |
/// | key.disregardSettings | true to ignore settings | not set| [#DISREGARD_SETTINGS_PROPERTY] |
///
/// Programmatically, you can use [#setBaseKeyConfigDir(Path)] or directly set [#currentPaths] to
/// ensure the correct paths. This
/// should be called once before something is done with KeY (e.g. before the `MainWindow` is
/// opened).
///
/// As of KeY 3.0, the configuration directory includes the major-minor version as a subdirectory
/// (e.g., `~/.key/3.0/`). This allows different KeY versions to maintain separate
/// configurations while still being able to fall back to previous version configurations when
/// upgrading.
///
/// @author weigl
public final class PathConfig {
    private static final Logger LOGGER = LoggerFactory.getLogger(PathConfig.class);

    /// The name of the Java system property used to indicate that the settings in the KeY directory
    /// should not be consulted at startup.
    public static final String DISREGARD_SETTINGS_PROPERTY = "key.disregardSettings";

    /// Indicator that the settings in the KeY directory should not be consulted at startup.
    public static final boolean DISREGARD_SETTINGS =
        Boolean.getBoolean(PathConfig.DISREGARD_SETTINGS_PROPERTY);

    ///
    ///
    public static final String KEY_HOME_PROPERTY = "key.home";

    ///
    public static final String KEY_CONFIG_PROPERTY = "key.config";

    /// The default name of the directory that contains KeY settings.
    public static final String KEY_DIRECTORY_NAME = ".key";

    public static final Comparator<Path> VERSION_COMPARATOR = (v1, v2) -> {
        String s1 = v1.getFileName().toString().substring(1);
        String s2 = v2.getFileName().toString().substring(1);
        int[] parts1 = Arrays.stream(s1.split("\\.")).mapToInt(Integer::parseInt).toArray();
        int[] parts2 = Arrays.stream(s2.split("\\.")).mapToInt(Integer::parseInt).toArray();
        return Arrays.compare(parts1, parts2);
    };


    ///
    public static Path getSettingsFile(String fileName) {
        var path = currentPaths.keyConfigDir.resolve(fileName);
        var old = previousPaths.keyConfigDir.resolve(fileName);
        if (!Files.exists(path) && Files.exists(old)) {
            try {
                Files.copy(old, path);
            } catch (IOException e) {
                LOGGER.warn("Could not copy {} to {}", old, path, e);
            }
        }
        return path;
    }

    public static final class KeyPaths {
        /// Directory where to find the KeY configuration files.
        // public Path baseKeyConfigDir;

        /// Directory where to find the KeY configuration files.
        /// This includes the version subdirectory (e.g., \~/.key/3.0/).
        public Path keyConfigDir;

        /// In which file to store the recent files.
        public Path recentFileStorage;
        /// In which file to store the proof-independent settings.
        public Path proofIndependentSettings;
        /// Directory in which the log files are stored.
        public Path logDirectory;

        KeyPaths(Path keyConfigDir) {
            this.keyConfigDir = keyConfigDir;
            recentFileStorage = keyConfigDir.resolve("recentFiles_v2.json");
            proofIndependentSettings = keyConfigDir.resolve("proofIndependentSettings.json");
            logDirectory = keyConfigDir.resolve("logs");
        }
    }

    public static KeyPaths currentPaths;

    public static KeyPaths previousPaths;

    private PathConfig() {
    }

    /*
     * Initializes the instance variables with the default settings.
     */
    static {
        try {
            String manualConfigPath = System.getProperty(KEY_CONFIG_PROPERTY);
            if (manualConfigPath != null) {
                Paths.get(manualConfigPath);
            } else {
                final var manualConfigHome = System.getProperty(KEY_HOME_PROPERTY);
                if (manualConfigHome != null) {
                    Path basePath = Paths.get(manualConfigHome);
                    setBaseKeyConfigDir(basePath);
                } else {
                    String homeDir = System.getProperty("user.home");
                    if (homeDir == null) {
                        // weigl: logging/logger might not initialize at this early stage of key.
                        // Fallback to syserr
                        System.err.println(
                            "!!! WARN !!! `user.home` is not given by Java Runtime Environment. Strange.");
                        System.err.println(
                            "!!! WARN !!! Fallback: We are using the current working directory for a substitution.");
                        homeDir = ".";
                    }
                    var homePath = Paths.get(homeDir);

                    if (!Files.exists(homePath)) {
                        System.err.format("!!! WARN !!! user's home `%s` does not exists.%n",
                            homePath);
                        System.err.println(
                            "!!! WARN !!! Fallback: We are using the current working directory for a substitution.");
                        homePath = Paths.get(".");
                    }

                    if (!Files.isDirectory(homePath)) {
                        System.err.format(
                            "!!! WARN !!! user's home `%s` does not point to a directory.%n",
                            homePath);
                        System.err.println(
                            "!!! WARN !!! Fallback: We are using the current working directory for a substitution.");
                        homePath = Paths.get(".");
                    }

                    Path basePath = homePath.resolve(KEY_DIRECTORY_NAME);
                    setBaseKeyConfigDir(basePath);
                }
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    ///
    public static void setBaseKeyConfigDir(Path basePath) throws IOException {
        currentPaths = getWritingPaths(basePath);
        // if the folder does not exist or is empty, use the previous if possible for reading the
        // initial config
        previousPaths = getReadingPath(basePath);
    }

    // Resolves the path `<key.home>/v<major>.<minor>` and creates it if necessary.
    private static KeyPaths getWritingPaths(Path base) throws IOException {
        var currentVersion = KeYResourceManager.getManager().getVersion().split("\\.");
        var currentVersionCandidate = "v%s.%s".formatted(currentVersion[0], currentVersion[1]);
        var currentVersionPath = base.resolve(currentVersionCandidate);
        if (!Files.exists(currentVersionPath)) {
            Files.createDirectories(currentVersionPath);
        }
        return new KeyPaths(currentVersionPath);
    }

    private static KeyPaths getReadingPath(Path base) {
        Path prev = base;
        try (Stream<Path> stream = Files.list(base)) {
            prev = stream
                    .filter(Objects::nonNull)
                    .filter(it -> it.getFileName().toString().matches("v\\d+\\.\\d+"))
                    .filter(Files::isDirectory)
                    .filter(it -> !Objects.equals(it, currentPaths.keyConfigDir))
                    .filter(it -> {
                        try (Stream<Path> entries = Files.list(it)) {
                            return entries.findAny().isPresent();
                        } catch (IOException e) {
                            return false;
                        }
                    })
                    .max(VERSION_COMPARATOR)
                    .orElse(base);
            return new KeyPaths(prev);
        } catch (IOException ignored) {
        }
        return new KeyPaths(prev);
    }


    public static boolean isDifferentReadWriteDirectories() {
        return !Objects.equals(currentPaths.keyConfigDir, previousPaths.keyConfigDir);
    }
}
