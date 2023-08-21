/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.zip.ZipFile;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This dialog allows the user to select the proof to load from a proof bundle.
 *
 * @author Wolfram Pfeifer
 */
public final class ProofSelectionDialog extends JDialog {

    private static final long serialVersionUID = -586107341789859969L;
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofSelectionDialog.class);

    /**
     * Regex for identifiers (class, method), which catches for example "java.lang.Object",
     * "SumAndMax", "sort(int[] a)", ...
     */
    private static final String IDENT = "(.*)";

    /**
     * Regex for the type of the contract (catches something like "JML normal_behavior operation
     * contract").
     */
    private static final String TYPE = "(.*)";

    /**
     * Regex for the number of the proof.
     */
    private static final String NUM = "(\\d+)";

    /**
     * The pattern to match the filename of the proof.
     */
    private static final Pattern PROOF_NAME_PATTERN = Pattern.compile(
        IDENT + "\\(" + IDENT + "__" + IDENT + "\\)\\)\\." + TYPE + "." + NUM + ".proof");

    /**
     * The path of the proof to load (relative to the root of the proof bundle, so actually just the
     * filename of the proof file inside the bundle).
     */
    private Path proofToLoad;

    /**
     * Creates a new ProofSelectionDialog for the given proof
     *
     * @param bundlePath the path of the proof bundle to load
     * @throws IOException if the proof bundle can not be read
     */
    private ProofSelectionDialog(Path bundlePath) throws IOException {
        super(MainWindow.getInstance(), "Choose proof to load", true);

        // create and fill list with proofs available for loading
        JList<Path> list = createAndFillList(bundlePath);

        // create scroll pane with list
        JScrollPane scrollPane = new JScrollPane(list);
        scrollPane.setBorder(new TitledBorder("Proofs found in bundle:"));
        getContentPane().setLayout(new BorderLayout());
        getContentPane().add(scrollPane, BorderLayout.CENTER);

        // create panel with buttons
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        getContentPane().add(buttonPanel, BorderLayout.PAGE_END);

        // create "Ok" button
        JButton okButton = new JButton("OK");
        Dimension buttonDim = new Dimension(100, 27);
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(e -> {
            proofToLoad = list.getSelectedValue();
            setVisible(false);
            dispose();
        });
        // disable "Ok" button if no proof was found
        if (list.getModel().getSize() == 0) {
            okButton.setEnabled(false);
        }
        buttonPanel.add(okButton);
        getRootPane().setDefaultButton(okButton);

        // create "Cancel" button
        JButton cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(e -> {
            setVisible(false);
            dispose();
        });
        buttonPanel.add(cancelButton);

        setMinimumSize(new Dimension(300, 200));
        pack();
    }

    /**
     * Creates a JList and fills it with the proofs found in the bundle.
     *
     * @param bundlePath the path of the proof bundle
     * @return the created JList
     * @throws IOException if the proof bundle can not be read
     */
    private JList<Path> createAndFillList(Path bundlePath) throws IOException {
        // create a list of all *.proof files (only top level in bundle)
        List<Path> proofs;
        // read zip
        try (ZipFile bundle = new ZipFile(bundlePath.toFile())) {
            proofs = bundle.stream().filter(e -> !e.isDirectory())
                    .filter(e -> e.getName().endsWith(".proof")).map(e -> Paths.get(e.getName()))
                    .collect(Collectors.toList());
        }



        // show the list in a JList
        DefaultListModel<Path> model = new DefaultListModel<>();
        for (Path p : proofs) {
            model.addElement(p);
        }
        JList<Path> list = new JList<>(model);
        list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        list.setSelectedIndex(0);
        list.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent mouseEvent) {
                if (mouseEvent.getClickCount() >= 2) {
                    proofToLoad = list.getSelectedValue();
                    setVisible(false);
                    dispose();
                }
            }
        });
        list.setCellRenderer((jList, value, index, isSelected, cellHasFocus) -> {
            JLabel label = new JLabel(abbreviateProofPath(value));
            label.setOpaque(true); // allows for color changes via setSelectionBackground()
            if (isSelected) {
                label.setBackground(list.getSelectionBackground());
                label.setForeground(list.getSelectionForeground());
            } else {
                label.setBackground(list.getBackground());
                label.setForeground(list.getForeground());
            }
            return label;
        });
        return list;
    }

    /**
     * Abbreviates the filename of the proof if it matches the usual KeY format.
     *
     * @param proofPath the path (actually only the filename) of the proof
     * @return the abbreviated proof name if it matches, the given path as String otherwise
     */
    private static String abbreviateProofPath(Path proofPath) {

        final String pathString = proofPath.toString();
        Matcher m = PROOF_NAME_PATTERN.matcher(pathString);
        if (m.matches() && m.groupCount() == 5) {
            String className = m.group(1);
            String method = m.group(3);
            String type = m.group(4).toLowerCase();
            String num = m.group(5);

            // type is either "normal", "exceptional", or empty
            if (type.contains("normal")) {
                type = "normal ";
            } else if (type.contains("exceptional")) {
                type = "exceptional ";
            } else {
                type = "";
            }

            return className + "::" + method + ") " + type + num;
        }
        // fallback: use complete filename
        return pathString;
    }

    /**
     * Shows the dialog with the given path and returns the filename of the proof to load.
     *
     * @param bundlePath the path of the proof bundle
     * @return the filename of the proof to load
     */
    private static Path showDialog(Path bundlePath) {
        Path proofPath = null;
        try {
            ProofSelectionDialog dialog = new ProofSelectionDialog(bundlePath);
            dialog.setLocationRelativeTo(MainWindow.getInstance()); // center dialog
            dialog.setVisible(true);
            proofPath = dialog.proofToLoad;
        } catch (IOException exc) {
            LOGGER.error("", exc);
            IssueDialog.showExceptionDialog(MainWindow.getInstance(), exc);
        }
        return proofPath;
    }

    /**
     * Shows a dialog and allows the user to choose the proof to load from a bundle.
     *
     * @param bundlePath the path of the proof bundle that is loaded
     * @return the path of the proof relative to the bundle (proofs are always top level, which
     *         means the returned path will only contains the filename of the proof file) or null if
     *         the given path does not denote a bundle
     */
    public static Path chooseProofToLoad(Path bundlePath) {
        if (isProofBundle(bundlePath)) {
            return showDialog(bundlePath);
        }
        return null;
    }

    /**
     * Checks if a path denotes a proof bundle.
     *
     * @param path the path to check
     * @return true iff the path denotes a proof bundle
     */
    public static boolean isProofBundle(Path path) {
        return path.toString().endsWith(".zproof");
    }
}
