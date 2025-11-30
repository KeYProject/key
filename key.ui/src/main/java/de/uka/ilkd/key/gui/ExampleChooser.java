/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;

import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

import org.key_project.util.java.IOUtil;

import org.jspecify.annotations.Nullable;
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
    private Path fileToLoad = null;

    /**
     * The currently selected example. <code>null</code> if none selected
     */
    private Example selectedExample;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    private ExampleChooser(Path examplesDir) {
        super(MainWindow.getInstance(), "Load Example", true);
        assert examplesDir != null;

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

        // create the checkbox to hide example load on next startup
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        JCheckBox showAgainCheckbox =
            new JCheckBox("Show this dialog on startup", vs.getShowLoadExamplesDialog());
        buttonPanel.add(showAgainCheckbox);
        showAgainCheckbox.addActionListener(e -> {
            vs.setShowLoadExamplesDialog(showAgainCheckbox.isSelected());
        });

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

    public static Path lookForExamples() {
        // weigl: using java properties: -Dkey.examples.dir="..."
        if (System.getProperty(KEY_EXAMPLE_DIR) != null) {
            return Paths.get(System.getProperty(KEY_EXAMPLE_DIR));
        }

        // greatly simplified version without parent path lookup.
        File folder = new File(IOUtil.getProjectRoot(ExampleChooser.class), EXAMPLES_PATH);
        if (!folder.exists()) {
            folder = new File(IOUtil.getClassLocation(ExampleChooser.class), EXAMPLES_PATH);
        }
        return folder.toPath();
    }

    private static String fileAsString(Path f) {
        try {
            return Files.readString(f);
        } catch (IOException e) {
            LOGGER.error("Could not read file '{}'", f, e);
            return "<Error reading file: " + f + ">";
        }
    }


    private void updateDescription() {

        TreePath selectionPath = exampleList.getSelectionModel().getSelectionPath();
        if (selectionPath == null) {
            return;
        }

        DefaultMutableTreeNode node = (DefaultMutableTreeNode) selectionPath.getLastPathComponent();
        Object nodeObj = node.getUserObject();
        tabPane.removeAll();

        if (nodeObj instanceof Example example) {

            if (example != selectedExample) {
                addTab(example.getDescription(), "Description", true);
                final String fileAsString = fileAsString(example.getObligationFile());
                final int p = fileAsString.lastIndexOf("\\problem");
                if (p >= 0) {
                    addTab(fileAsString.substring(p), "Proof Obligation", false);
                }
                for (Path file : example.getAdditionalFiles()) {
                    addTab(fileAsString(file), file.getFileName().toString(), false);
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
    public static @Nullable Path showInstance(Path examplesDirString) {
        // get examples directory
        Path examplesDir;
        if (examplesDirString == null) {
            examplesDir = lookForExamples();
        } else {
            examplesDir = examplesDirString;
        }

        if (!Files.isDirectory(examplesDir)) {
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
    public static List<Example> listExamples(Path examplesDir) {
        List<Example> result = new ArrayList<>(64);

        final Path index = examplesDir.resolve("index").resolve("samplesIndex.txt");
        try {
            for (var line : Files.readAllLines(index)) {
                line = line.trim();
                if (line.startsWith("#") || line.isEmpty()) {
                    continue;
                }
                Path f = examplesDir.resolve(line);
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
