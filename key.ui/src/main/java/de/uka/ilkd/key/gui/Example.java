/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.Properties;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class wraps a {@link java.io.File} and has a special {@link #toString()} method only using
 * the
 * short file name w/o path.
 * <p>
 * Used for displaying files in the examples list w/o prefix
 */
public class Example {
    private static final Logger LOGGER = LoggerFactory.getLogger(Example.class);
    /**
     * This constant is accessed by the eclipse based projects.
     */
    public static final String KEY_FILE_NAME = "project.key";

    private static final String PROOF_FILE_NAME = "project.proof";

    /**
     * The default category under which examples range if they do not have {@link #KEY_PATH}
     * set.
     */
    public static final String DEFAULT_CATEGORY_PATH = "Unsorted";

    /**
     * The {@link Properties} key to specify the path in the tree.
     */
    public static final String KEY_PATH = "example.path";

    /**
     * The {@link Properties} key to specify the name of the example. Directory name if left
     * open.
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
     * The {@link Properties} key to specify the path in the tree. Prefix to specify additional
     * files to load. Append 1, 2, 3, ...
     */
    public static final String ADDITIONAL_FILE_PREFIX = "example.additionalFile.";

    /**
     * The {@link Properties} key to specify the path in the tree. Prefix to specify export
     * files which are not shown as tabs in the example wizard but are extracted to Java
     * projects in the Eclipse integration. Append 1, 2, 3, ...
     */
    public static final String EXPORT_FILE_PREFIX = "example.exportFile.";

    public final Path exampleFile;
    public final Path directory;
    public final String description;
    public final Properties properties;

    public Example(Path file) throws IOException {
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

    public String[] getPath() {
        return properties.getProperty(KEY_PATH, DEFAULT_CATEGORY_PATH).split("/");
    }

    @Override
    public String toString() {
        return getName();
    }

    public void addToTreeModel(DefaultTreeModel model) {
        DefaultMutableTreeNode node =
            findChild((DefaultMutableTreeNode) model.getRoot(), getPath(), 0);
        node.add(new DefaultMutableTreeNode(this));
    }

    private DefaultMutableTreeNode findChild(DefaultMutableTreeNode root, String[] path,
            int from) {
        if (from == path.length) {
            return root;
        }
        Enumeration<?> en = root.children();
        while (en.hasMoreElements()) {
            DefaultMutableTreeNode node = (DefaultMutableTreeNode) en.nextElement();
            if (node.getUserObject().equals(path[from])) {
                return findChild(node, path, from + 1);
            }
        }
        // not found ==> add new
        DefaultMutableTreeNode node = new DefaultMutableTreeNode(path[from]);
        root.add(node);
        return findChild(node, path, from + 1);
    }

    public boolean hasProof() {
        return properties.containsKey(KEY_PROOF_FILE);
    }

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
