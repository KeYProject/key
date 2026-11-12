/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * One example of the example chooser: wraps the index file of an example directory and parses the
 * small property header (name, category path, obligation/proof file, additional files) plus the
 * free-form description. Counter-part of {@code de.uka.ilkd.key.gui.Example} in the Swing module
 * {@code key.ui}; the Swing class additionally carries the Swing tree-model integration
 * ({@code addToTreeModel}/{@code findChild}), which the JavaFX port realizes with JavaFX tree
 * items in {@link ExampleChooserF}.
 */
public final class ExampleF {

    private static final Logger LOGGER = LoggerFactory.getLogger(ExampleF.class);

    /**
     * This constant is accessed by the eclipse based projects.
     */
    public static final String KEY_FILE_NAME = "project.key";

    private static final String PROOF_FILE_NAME = "project.proof";

    /**
     * The default category under which examples range if they do not have {@link #KEY_PATH} set.
     */
    public static final String DEFAULT_CATEGORY_PATH = "Unsorted";

    /**
     * The {@link Properties} key to specify the path in the tree.
     */
    public static final String KEY_PATH = "example.path";

    /**
     * The {@link Properties} key to specify the name of the example. Directory name if left open.
     */
    public static final String KEY_NAME = "example.name";

    /**
     * The {@link Properties} key to specify the file for the example. KEY_FILE_NAME by default
     */
    public static final String KEY_FILE = "example.file";

    /**
     * The {@link Properties} key to specify the proof file in the tree. May be left open
     */
    public static final String KEY_PROOF_FILE = "example.proofFile";

    /**
     * The {@link Properties} key prefix to specify additional files to load. Append 1, 2, 3, ...
     */
    public static final String ADDITIONAL_FILE_PREFIX = "example.additionalFile.";

    /**
     * The {@link Properties} key prefix to specify export files which are not shown as tabs in
     * the example wizard but are extracted to Java projects in the Eclipse integration. Append
     * 1, 2, 3, ...
     */
    public static final String EXPORT_FILE_PREFIX = "example.exportFile.";

    /** The index file (usually {@code project.key}) that was parsed. */
    private final Path exampleFile;
    /** The directory containing the example. */
    private final Path directory;
    /** The description: every line of the index file after the first empty line. */
    private final String description;
    /** The parsed properties header of the index file. */
    private final Properties properties;

    /**
     * Creates an example for the given index file and parses its header and description.
     *
     * @param file the index file of the example ({@code project.key} by default)
     * @throws IOException if the file cannot be read
     */
    public ExampleF(Path file) throws IOException {
        this.exampleFile = file;
        this.directory = file.getParent();
        this.properties = new Properties();
        StringBuilder sb = new StringBuilder();
        extractDescription(file, sb, properties);
        this.description = sb.toString();
    }

    public Path getDirectory() {
        return directory;
    }

    public Path getProofFile() {
        return directory.resolve(properties.getProperty(KEY_PROOF_FILE, PROOF_FILE_NAME));
    }

    public Path getObligationFile() {
        return directory.resolve(properties.getProperty(KEY_FILE, KEY_FILE_NAME));
    }

    public String getName() {
        return properties.getProperty(KEY_NAME, directory.getFileName().toString());
    }

    public String getDescription() {
        return description;
    }

    public Path getExampleFile() {
        return exampleFile;
    }

    public List<Path> getAdditionalFiles() {
        var result = new ArrayList<Path>();
        int i = 1;
        while (properties.containsKey(ADDITIONAL_FILE_PREFIX + i)) {
            result.add(directory.resolve(properties.getProperty(ADDITIONAL_FILE_PREFIX + i)));
            i++;
        }
        return result;
    }

    public List<Path> getExportFiles() {
        var result = new ArrayList<Path>();
        int i = 1;
        while (properties.containsKey(EXPORT_FILE_PREFIX + i)) {
            result.add(directory.resolve(properties.getProperty(EXPORT_FILE_PREFIX + i)));
            i++;
        }
        return result;
    }

    /**
     * @return the category path segments under which the example is shown in the chooser tree
     */
    public String[] getPath() {
        return properties.getProperty(KEY_PATH, DEFAULT_CATEGORY_PATH).split("/");
    }

    /**
     * @return whether the example directory declares a proof file ({@code example.proofFile})
     */
    public boolean hasProof() {
        return properties.containsKey(KEY_PROOF_FILE);
    }

    @Override
    public String toString() {
        return getName();
    }

    /**
     * Parses the index file: lines before the first empty line are {@code key: value} property
     * entries (comment lines starting with {@code #} are skipped), everything after the first
     * empty line is the description (Swing {@code Example.extractDescription}).
     */
    private static StringBuilder extractDescription(Path file, StringBuilder sb,
            Properties properties) {
        try {
            boolean emptyLineSeen = false;
            for (var line : Files.readAllLines(file, StandardCharsets.UTF_8)) {
                if (emptyLineSeen) {
                    sb.append(line).append("\n");
                } else {
                    String trimmed = line.trim();
                    if (trimmed.isEmpty()) {
                        emptyLineSeen = true;
                    } else {
                        if (!trimmed.startsWith("#")) {
                            String[] entry = trimmed.split(" *[:=] *", 2);
                            if (entry.length > 1) {
                                properties.put(entry[0], entry[1]);
                            }
                        }
                    }
                }
            }
        } catch (IOException e) {
            LOGGER.error("", e);
            return sb;
        }
        return sb;
    }
}
