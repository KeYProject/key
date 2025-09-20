/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Objects;

/**
 * This class manages the different paths in the output folder.
 *
 * @author Alexander Weigl
 * @version 1 (02.02.24)
 */
public record OutputEnvironment(Path targetFolder, boolean onlyTestDir) {
    /**
     * Returns the source code folder
     */
    public Path getSourceDir() {
        return targetFolder.resolve("src/main/java");
    }

    /**
     * Returns the test code folder
     */
    public Path getTestSourceDir() {
        if (onlyTestDir) {
            return targetFolder;
        }
        return targetFolder.resolve("src/test/java");
    }

    /**
     * Returns the path to the ANT build.xml file
     */
    public Path getAntFile() {
        return targetFolder.resolve("build.xml");
    }

    /**
     * Returns the path to the ANT build.xml file
     */
    public Path getGradleFile() {
        return targetFolder.resolve("build.gradle.kts");
    }

    /**
     * Returns the path to the pom.xml for Maven file
     */
    public Path getMavenFile() {
        return targetFolder.resolve("pom.xml");
    }


    /**
     * Returns the path to the README.md file
     */
    public Path getReadmeFile() {
        return targetFolder.resolve("README.md");
    }

    /**
     * Initialize/create the necessary directories.
     *
     * @throws IOException if the output folder is not write or the folders can not be created.
     */
    public void init() throws IOException {
        Files.createDirectories(getTestSourceDir());
        if (!onlyTestDir) {
            Files.createDirectories(getSourceDir());
            installProjectFile();
        }
    }

    private void installProjectFile() throws IOException {
        if (!Files.exists(getAntFile())) {
            try (var buildXml = getClass().getResourceAsStream("/de/uka/ilkd/key/tcg/build.xml")) {
                Files.copy(Objects.requireNonNull(buildXml), getAntFile());
            }
        }

        if (!Files.exists(getMavenFile())) {
            try (var pomXml = getClass().getResourceAsStream("/de/uka/ilkd/key/tcg/pom.xml")) {
                Files.copy(Objects.requireNonNull(pomXml), getMavenFile());
            }
        }

        if (!Files.exists(getGradleFile())) {
            try (var gradleKts =
                getClass().getResourceAsStream("/de/uka/ilkd/key/tcg/build.gradle.kts")) {
                Files.copy(Objects.requireNonNull(gradleKts), getGradleFile());
            }
        }
    }
}
