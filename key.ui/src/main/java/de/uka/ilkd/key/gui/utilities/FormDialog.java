/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;
import javax.swing.*;

import de.uka.ilkd.key.util.Pair;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Simple and generic input form dialog. Support {@link JTextField} and {@link JTextArea} as fields.
 *
 * @author Arne Keller
 */
public class FormDialog extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(FormDialog.class);

    /**
     * Construct and show a new form.
     *
     * @param owner parent dialog
     * @param title title of the form
     * @param comps components of the dialog: (name, input element)
     * @param validate validation function (return a non-null string if there is an error)
     * @param onSubmit callback for submit action
     * @param onCancel callback for cancel action
     */
    public FormDialog(JDialog owner, String title, List<Pair<String, JComponent>> comps,
            Function<List<Pair<String, String>>, String> validate,
            Consumer<List<Pair<String, String>>> onSubmit, Runnable onCancel) {
        super(owner);

        setTitle(title);
        setModal(true);
        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);

        JPanel mainPane = new JPanel();
        mainPane.setLayout(new GridBagLayout());

        var c = new GridBagConstraints();
        c.insets.bottom = 10;
        c.insets.top = 10;
        c.insets.left = 10;
        c.insets.right = 10;
        c.gridy = 1;
        c.anchor = GridBagConstraints.WEST;

        for (var comp : comps) {
            c.gridx = 1;
            mainPane.add(new JLabel(comp.first), c.clone());
            c.gridx = 2;
            c.fill = GridBagConstraints.HORIZONTAL;
            mainPane.add(comp.second, c.clone());

            c.gridy++;
        }

        var submit = new JButton("Submit");
        submit.addActionListener(e -> {
            try {
                List<Pair<String, String>> data = new ArrayList<>();
                for (var comp : comps) {
                    data.add(new Pair<>(comp.first, extractValue(comp.second)));
                }
                var error = validate.apply(data);
                if (error != null) {
                    JOptionPane.showMessageDialog(this, error, "Validation error",
                        JOptionPane.ERROR_MESSAGE);
                    return;
                }
                onSubmit.accept(data);
                dispose();
            } catch (Exception err) {
                LOGGER.error("submit action failed ", err);
            }
        });

        var cancel = new JButton("Cancel");
        cancel.addActionListener(e -> {
            onCancel.run();
            dispose();
        });

        JPanel buttonPane = new JPanel();
        buttonPane.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        buttonPane.add(submit);
        buttonPane.add(cancel);

        c.gridx = 2;
        c.insets = new Insets(5, 5, 5, 5);
        mainPane.add(buttonPane, c);

        setContentPane(mainPane);
        pack();
        setLocationRelativeTo(owner);
        setVisible(true);
    }

    private static String extractValue(JComponent comp) {
        if (comp instanceof JTextArea) {
            return ((JTextArea) comp).getText();
        } else if (comp instanceof JTextField) {
            return ((JTextField) comp).getText();
        } else {
            throw new IllegalStateException("FormDialog used with incorrect component");
        }
    }
}
