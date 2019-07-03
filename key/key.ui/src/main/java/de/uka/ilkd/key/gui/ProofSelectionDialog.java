package de.uka.ilkd.key.gui;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;
import java.util.stream.Collectors;
import java.util.zip.ZipFile;

/**
 * When loading a proof bundle, this dialog allows the user to select the proof to load.
 *
 * @author Wolfram Pfeifer
 */
public final class ProofSelectionDialog extends JDialog {
    /**
     * The name of the proof to load.
     */
    private String proofToLoad;

    /**
     * Creates and shows a new
     * @param parent the parent of this dialog (blocked until this dialog is closed)
     * @param bundlePath the path of the proof bundle to load
     * @throws IOException if the proof bundle can not be read for some reason
     */
    public ProofSelectionDialog(Frame parent, Path bundlePath) throws IOException {
        super(parent, "Choose proof to load", true);

        // read zip
        ZipFile bundle = new ZipFile(bundlePath.toFile());

        // create a list of all *.proof files (only top level in bundle)
        List proofs = bundle.stream()
                            .filter(e -> !e.isDirectory())
                            .filter(e -> e.getName().endsWith(".proof"))  // *.key not allowed!
                            .map(e -> e.getName())
                            .collect(Collectors.toList());

        // show list in a JList
        DefaultListModel<String> model = new DefaultListModel<>();
        model.addAll(proofs);
        JList<String> list = new JList<>(model);
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
        list.setCellRenderer(new ListCellRenderer<String>() {
            @Override
            public Component getListCellRendererComponent(JList<? extends String> jList,
                                                          String value,
                                                          int index,
                                                          boolean isSelected,
                                                          boolean cellHasFocus) {
                JLabel label = new JLabel();
                label.setOpaque(true); // allows for color changes via setSelectionBackground()
                if (isSelected) {
                    label.setBackground(list.getSelectionBackground());
                    label.setForeground(list.getSelectionForeground());
                } else {
                    label.setBackground(list.getBackground());
                    label.setForeground(list.getForeground());
                }

                String[] parts = value.split("\\.");
                if (parts.length < 3) {
                    return label;
                }

                // extract relevant parts of the filename, that is
                // class name, method name, type of the contract, and number
                int i0 = parts[0].indexOf('(');
                int i1 = parts[0].indexOf("__") + 2;
                int i2 = parts[0].indexOf(')', i1) + 1;
                int i3 = parts[1].indexOf(' ') + 1;
                int i4 = parts[1].indexOf(' ', i3);
                i4 = Math.min(i4, parts[1].indexOf('_', i3));
                String className = parts[0].substring(0, i0);
                String methodName = parts[0].substring(i1, i2);
                String type = parts[1].substring(i3, i4);
                String number = parts[2];
                String text = className + "::" + methodName + " " + type + " " + number;
                label.setText(text);
                return label;
            }
        });

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
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                proofToLoad = list.getSelectedValue();
                setVisible(false);
                dispose();
            }
        });
        buttonPanel.add(okButton);
        getRootPane().setDefaultButton(okButton);

        // create "Cancel" button
        JButton cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                setVisible(false);
                dispose();
            }
        });
        buttonPanel.add(cancelButton);

        // show
        setMinimumSize(new Dimension(300, 200));
        pack();
        setLocationRelativeTo(parent);
        setVisible(true);
    }

    public String getProofName() {
        return proofToLoad;
    }
}
