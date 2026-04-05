/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.examples;

import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.DefaultTreeModel;
import javax.swing.tree.TreePath;
import javax.swing.tree.TreeSelectionModel;
import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.File;
import java.nio.file.Path;
import java.util.List;

import static de.uka.ilkd.key.gui.examples.ExamplesFacade.fileAsString;

/**
 * Dialog to choose an example to load.
 * May be opened automatically when KeY starts.
 */
@NullMarked
public final class ExampleChooser extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(ExampleChooser.class);

    private final JTree exampleList = new JTree();
    private final JButton loadButton;
    private final JButton loadProofButton;
    private final JButton cancelButton;
    private final JTabbedPane tabPane;

    /**
     * The result value of the dialog. <code>null</code> if nothing to be loaded
     */
    private @Nullable Path fileToLoad = null;

    /**
     * The currently selected example. <code>null</code> if none selected
     */
    private @Nullable Example selectedExample;

    private ExampleChooser(Frame owner, File examplesDir) {
        super(owner, "Load Example", true);

        if (!examplesDir.isDirectory()) {
            throw new IllegalArgumentException(examplesDir + " is not a directory");
        }

        // create list panel
        final JPanel listPanel = new JPanel(new BorderLayout());
        getContentPane().add(listPanel);

        // create example list
        final DefaultTreeModel model = new DefaultTreeModel(new DefaultMutableTreeNode());
        List<Example> examples = ExamplesFacade.listExamples(examplesDir);
        for (Example example : examples) {
            example.addToTreeModel(model);
        }

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
        showAgainCheckbox.addActionListener(e ->
                vs.setShowLoadExamplesDialog(showAgainCheckbox.isSelected()));

        // create "load" button
        loadButton = new JButton("Load Example");
        loadButton.addActionListener(e -> {
            if (selectedExample == null) {
                throw new RuntimeException("No example selected");
            }
            fileToLoad = selectedExample.keyFile();
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
            fileToLoad = selectedExample.keyFile();
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
                final String fileAsString = ExamplesFacade.fileAsString(example.keyFile());
                final int p = fileAsString.lastIndexOf("\\problem");
                if (p >= 0) {
                    addTab(fileAsString.substring(p), "Proof Obligation", false);
                }
                for (Path file : example.additionalFiles()) {
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
    public static @Nullable File showInstance(Frame owner, @Nullable String examplesDirString) {
        // get examples directory
        File examplesDir;
        if (examplesDirString == null) {
            examplesDir = ExamplesFacade.lookForExamples();
        } else {
            examplesDir = new File(examplesDirString);
        }
        return showInstance(owner, examplesDir);
    }

    private static @Nullable File showInstance(Frame owner, File examplesDir) {
        if (!examplesDir.isDirectory()) {
            JOptionPane.showMessageDialog(owner,
                    "The examples directory cannot be found.\nPlease install them at %s".formatted(
                            examplesDir.getAbsolutePath()),
                "Error loading examples", JOptionPane.ERROR_MESSAGE);
            return null;
        }

        // show dialog
        var instance = new ExampleChooser(owner, examplesDir);
        instance.setLocationRelativeTo(instance.getOwner());
        instance.setVisible(true);

        // return result
        return instance.fileToLoad;
    }
}
