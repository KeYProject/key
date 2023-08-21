/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.*;
import java.util.List;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import de.uka.ilkd.key.gui.utilities.GuiUtilities;

import org.key_project.util.java.IOUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog to choose an example to load.
 * May be opened automatically when KeY starts.
 */
public final class ExampleChooser extends JDialog {
    /**
     * This path is also accessed by the Eclipse integration of KeY to find the right examples.
     */
    public static final String EXAMPLES_PATH = "examples";

    private static final long serialVersionUID = -4405666868752394532L;

    /**
     * This constant is accessed by the eclipse based projects.
     */
    public static final String KEY_FILE_NAME = "project.key";

    private static final String PROOF_FILE_NAME = "project.proof";

    /**
     * Java property name to specify a custom key example folder.
     */
    public static final String KEY_EXAMPLE_DIR = "key.examples.dir";

    private static final Logger LOGGER = LoggerFactory.getLogger(ExampleChooser.class);


    /**
     * This class is a singleton class and this its only instance.
     */
    private static ExampleChooser instance;

    private final JTree exampleList;
    private final JButton loadButton;
    private final JButton loadProofButton;
    private final JButton cancelButton;
    private final JTabbedPane tabPane;

    /**
     * The result value of the dialog. <code>null</code> if nothing to be loaded
     */
    private File fileToLoad = null;

    /**
     * The currently selected example. <code>null</code> if none selected
     */
    private Example selectedExample;

    /**
     * This class wraps a {@link File} and has a special {@link #toString()} method only using the
     * short file name w/o path.
     * <p>
     * Used for displaying files in the examples list w/o prefix
     */
    public static class Example {
        /**
         * The default category under which examples range if they do not have {@link #KEY_PATH}
         * set.
         */
        private static final String DEFAULT_CATEGORY_PATH = "Unsorted";

        /**
         * The {@link Properties} key to specify the path in the tree.
         */
        private static final String KEY_PATH = "example.path";

        /**
         * The {@link Properties} key to specify the name of the example. Directory name if left
         * open.
         */
        private static final String KEY_NAME = "example.name";

        /**
         * The {@link Properties} key to specify the file for the example. KEY_FILE_NAME by default
         */
        private static final String KEY_FILE = "example.file";

        /**
         * The {@link Properties} key to specify the proof file in the tree. May be left open
         */
        private static final String KEY_PROOF_FILE = "example.proofFile";

        /**
         * The {@link Properties} key to specify the path in the tree. Prefix to specify additional
         * files to load. Append 1, 2, 3, ...
         */
        private static final String ADDITIONAL_FILE_PREFIX = "example.additionalFile.";

        /**
         * The {@link Properties} key to specify the path in the tree. Prefix to specify export
         * files which are not shown as tabs in the example wizard but are extracted to Java
         * projects in the Eclipse integration. Append 1, 2, 3, ...
         */
        private static final String EXPORT_FILE_PREFIX = "example.exportFile.";

        private final File exampleFile;
        private final File directory;
        private final String description;
        private final Properties properties;

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
            ArrayList<File> result = new ArrayList<>();
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

    }

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private ExampleChooser(File examplesDir) {
        super(MainWindow.getInstance(), "Load Example", true);
        assert examplesDir != null;
        assert examplesDir.isDirectory();

        // create list panel
        final JPanel listPanel = new JPanel();
        listPanel.setLayout(new BorderLayout());
        getContentPane().add(listPanel);

        // create example list
        final DefaultTreeModel model = new DefaultTreeModel(new DefaultMutableTreeNode());
        List<Example> examples = listExamples(examplesDir);
        for (Example example : examples) {
            example.addToTreeModel(model);
        }

        exampleList = new JTree();
        exampleList.setModel(model);
        exampleList.getSelectionModel().setSelectionMode(TreeSelectionModel.SINGLE_TREE_SELECTION);
        exampleList.addTreeSelectionListener(e -> updateDescription());
        exampleList.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                // row is -1 when the user does not click on an entry but on the background
                int row = exampleList.getRowForLocation(e.getX(), e.getY());

                // Check that it is a double click on an item, not a folder or the background
                if (e.getClickCount() != 2 || row == -1 || selectedExample == null) {
                    return;
                }
                loadButton.doClick();
            }
        });
        final JScrollPane exampleScrollPane = new JScrollPane(exampleList);
        exampleScrollPane.setBorder(new TitledBorder("Examples"));

        // create description label
        tabPane = new JTabbedPane(JTabbedPane.TOP);

        JSplitPane split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);
        split.add(exampleScrollPane);
        split.add(tabPane);
        split.setDividerLocation(300);
        listPanel.add(split, BorderLayout.CENTER);

        // create button panel
        final JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        final Dimension buttonDim = new Dimension(140, 27);
        buttonPanel
                .setMaximumSize(new Dimension(Integer.MAX_VALUE, (int) buttonDim.getHeight() + 10));
        getContentPane().add(buttonPanel);

        // create "load" button
        loadButton = new JButton("Load Example");
        loadButton.addActionListener(e -> {
            if (selectedExample == null) {
                throw new RuntimeException("No example selected");
            }
            fileToLoad = selectedExample.getObligationFile();
            setVisible(false);
        });
        buttonPanel.add(loadButton);
        getRootPane().setDefaultButton(loadButton);

        // create "load proof" button
        loadProofButton = new JButton("Load Proof");
        loadProofButton.addActionListener(e -> {
            if (selectedExample == null) {
                throw new IllegalStateException("No example selected");
            }
            if (!selectedExample.hasProof()) {
                throw new IllegalStateException("Selected example has no proof.");
            }
            fileToLoad = selectedExample.getProofFile();
            setVisible(false);
        });
        buttonPanel.add(loadProofButton);

        // create "cancel" button
        cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(e -> {
            fileToLoad = null;
            setVisible(false);
        });
        buttonPanel.add(cancelButton);
        GuiUtilities.attachClickOnEscListener(cancelButton);

        // select first example
        DefaultMutableTreeNode firstLeaf =
            ((DefaultMutableTreeNode) model.getRoot()).getFirstLeaf();
        TreePath pathToFirstLeaf = new TreePath(firstLeaf.getPath());
        exampleList.getSelectionModel().setSelectionPath(pathToFirstLeaf);
        exampleList.makeVisible(pathToFirstLeaf);

        // show
        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
        setSize(800, 400);
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    public static File lookForExamples() {
        // weigl: using java properties: -Dkey.examples.dir="..."
        if (System.getProperty(KEY_EXAMPLE_DIR) != null) {
            return new File(System.getProperty(KEY_EXAMPLE_DIR));
        }

        // greatly simplified version without parent path lookup.
        File folder = new File(IOUtil.getProjectRoot(ExampleChooser.class), EXAMPLES_PATH);
        if (!folder.exists()) {
            folder = new File(IOUtil.getClassLocation(ExampleChooser.class), EXAMPLES_PATH);
        }
        return folder;
    }

    private static String fileAsString(File f) {
        try {
            return IOUtil.readFrom(f);
        } catch (IOException e) {
            LOGGER.error("Could not read file '{}'", f, e);
            return "<Error reading file: " + f + ">";
        }
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


    private void updateDescription() {

        TreePath selectionPath = exampleList.getSelectionModel().getSelectionPath();
        if (selectionPath == null) {
            return;
        }

        DefaultMutableTreeNode node = (DefaultMutableTreeNode) selectionPath.getLastPathComponent();
        Object nodeObj = node.getUserObject();
        tabPane.removeAll();

        if (nodeObj instanceof Example) {
            Example example = (Example) nodeObj;

            if (example != selectedExample) {
                addTab(example.getDescription(), "Description", true);
                final String fileAsString = fileAsString(example.getObligationFile());
                final int p = fileAsString.lastIndexOf("\\problem");
                if (p >= 0) {
                    addTab(fileAsString.substring(p), "Proof Obligation", false);
                }
                for (File file : example.getAdditionalFiles()) {
                    addTab(fileAsString(file), file.getName(), false);
                }
                loadButton.setEnabled(true);
                loadProofButton.setEnabled(example.hasProof());
                selectedExample = example;
            }
        } else {
            selectedExample = null;
            loadButton.setEnabled(false);
            loadProofButton.setEnabled(false);
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    private void addTab(String string, String name, boolean wrap) {
        JTextArea area = new JTextArea();
        area.setText(string);
        area.setFont(new Font(Font.MONOSPACED, Font.PLAIN, area.getFont().getSize()));
        area.setCaretPosition(0);
        area.setEditable(false);
        area.setWrapStyleWord(true);
        area.setLineWrap(wrap);
        tabPane.add(new JScrollPane(area), name);
    }

    /**
     * Shows the dialog, using the passed examples directory. If null is passed, tries to find
     * examples directory on its own.
     */
    public static File showInstance(String examplesDirString) {
        // get examples directory
        File examplesDir;
        if (examplesDirString == null) {
            examplesDir = lookForExamples();
        } else {
            examplesDir = new File(examplesDirString);
        }

        if (!examplesDir.isDirectory()) {
            JOptionPane.showMessageDialog(MainWindow.getInstance(),
                "The examples directory cannot be found.\n" + "Please install them at "
                    + (examplesDirString == null ? IOUtil.getProjectRoot(ExampleChooser.class) + "/"
                            : examplesDirString),
                "Error loading examples", JOptionPane.ERROR_MESSAGE);
            return null;
        }

        // show dialog
        if (instance == null) {
            instance = new ExampleChooser(examplesDir);
        }
        instance.setLocationRelativeTo(instance.getOwner());
        instance.setVisible(true);

        // return result
        return instance.fileToLoad;
    }

    /**
     * Lists all examples in the given directory. This method is also accessed by the eclipse based
     * projects.
     *
     * @param examplesDir The examples directory to list examples in.
     * @return The found examples.
     */
    public static List<Example> listExamples(File examplesDir) {
        List<Example> result = new LinkedList<>();

        String line;
        final File index = new File(new File(examplesDir, "index"), "samplesIndex.txt");
        try (BufferedReader br =
            new BufferedReader(new FileReader(index, StandardCharsets.UTF_8))) {
            while ((line = br.readLine()) != null) {
                line = line.trim();
                if (line.startsWith("#") || line.length() == 0) {
                    continue;
                }
                File f = new File(examplesDir, line);
                try {
                    result.add(new Example(f));
                } catch (IOException e) {
                    LOGGER.warn("Cannot parse example {}; ignoring it.", f, e);
                }
            }
        } catch (IOException e) {
            LOGGER.warn("Error while reading samples", e);
        }
        return result;
    }
}
