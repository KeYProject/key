package de.uka.ilkd.key.gui;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.Properties;

/**
 * This class wraps a {@link java.io.File} and has a special {@link #toString()} method only using the
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

    public final File exampleFile;
    public final File directory;
    public final String description;
    public final Properties properties;

    public Example(File file) throws IOException {
        this.exampleFile = file;
        this.directory = file.getParentFile();
        this.properties = new Properties();
        StringBuilder sb = new StringBuilder();
        extractDescription(file, sb, properties);
        this.description = sb.toString();
    }

    public File getDirectory() {
        return directory;
    }

    public File getProofFile() {
        return new File(directory, properties.getProperty(KEY_PROOF_FILE, PROOF_FILE_NAME));
    }

    public File getObligationFile() {
        return new File(directory, properties.getProperty(KEY_FILE, KEY_FILE_NAME));
    }

    public String getName() {
        return properties.getProperty(KEY_NAME, directory.getName());
    }

    public String getDescription() {
        return description;
    }

    public File getExampleFile() {
        return exampleFile;
    }

    public List<File> getAdditionalFiles() {
        var result = new ArrayList<File>();
        int i = 1;
        while (properties.containsKey(ADDITIONAL_FILE_PREFIX + i)) {
            result.add(new File(directory, properties.getProperty(ADDITIONAL_FILE_PREFIX + i)));
            i++;
        }
        return result;
    }

    public List<File> getExportFiles() {
        ArrayList<File> result = new ArrayList<>();
        int i = 1;
        while (properties.containsKey(EXPORT_FILE_PREFIX + i)) {
            result.add(new File(directory, properties.getProperty(EXPORT_FILE_PREFIX + i)));
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

    private static StringBuilder extractDescription(File file, StringBuilder sb,
                                                    Properties properties) {
        try (BufferedReader r = new BufferedReader(new FileReader(file, StandardCharsets.UTF_8))) {
            String line;
            boolean emptyLineSeen = false;
            while ((line = r.readLine()) != null) {
                if (emptyLineSeen) {
                    sb.append(line).append("\n");
                } else {
                    String trimmed = line.trim();
                    if (trimmed.length() == 0) {
                        emptyLineSeen = true;
                    } else if (trimmed.startsWith("#")) {
                        // ignore
                    } else {
                        String[] entry = trimmed.split(" *[:=] *", 2);
                        if (entry.length > 1) {
                            properties.put(entry[0], entry[1]);
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