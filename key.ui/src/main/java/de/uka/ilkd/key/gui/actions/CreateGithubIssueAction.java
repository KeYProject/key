/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.IOException;
import java.net.URI;
import java.net.URLEncoder;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.util.Objects;
import java.util.stream.Collectors;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBrands;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.fonticons.IconProvider;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.KeYConstants;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This action allows the creation of Github issues with more ease.
 * <p>
 * It follows the current bug template and adds Java source and KeY version automatically.
 *
 * @author weigl
 */
public class CreateGithubIssueAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(CreateGithubIssueAction.class);
    private static final String URL = "https://github.com/keyproject/key/issues/new";

    public static final IconProvider ICON_GITHUB =
        new IconFontProvider(FontAwesomeBrands.GITHUB);

    public CreateGithubIssueAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Create Github Issue");
        setIcon(ICON_GITHUB.get());
    }

    @Override
    public void actionPerformed(ActionEvent event) {
        var body = """
                ## Description
                > Please describe your concern in detail!

                %JAVA%

                ## Reproducible

                > Is the issue reproducible?
                > Select one of: always, sometimes, random, have not tried, n/a

                ### Steps to reproduce
                > Describe the steps needed to reproduce the issue.

                1. ...
                2. ...
                3. ...
                > What is your expected behavior and what was the actual behavior?

                ### Additional information

                > Add more details here. In particular: if you have a stacktrace, put it here.
                ---
                * Commit: %CHECKSUM%
                """;

        String java = "";
        Proof proof = MainWindow.getInstance().getMediator().getSelectedProof();
        if (proof != null) {
            var javaSourceLocation = SendFeedbackAction.getJavaSourceLocation(proof);
            if (javaSourceLocation != null) {
                try (final var walker = Files.walk(javaSourceLocation)) {
                    java = walker.map(it -> {
                        try {
                            if (it.getFileName().toString().endsWith(".java")) {
                                return "* " + it.getFileName() + "\n```\n" + Files.readString(it)
                                    + "```\n";
                            }
                        } catch (IOException e) {
                        }
                        return null;
                    }).filter(Objects::nonNull)
                            .collect(Collectors.joining("\n"));
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }
            }
        }

        body = body.replace("%CHECKSUM%", KeYConstants.INTERNAL_VERSION)
                .replace("%JAVA%", java);

        URI uri = URI.create(URL + "?body=" + URLEncoder.encode(body, Charset.defaultCharset()));
        LOGGER.info("Opening URI: {}", uri);
        try {
            Desktop.getDesktop().browse(uri);
        } catch (IOException e) {
            LOGGER.error("Could not open browser for URI", e);
            showGeneratedTextDialog(body);
        }

    }

    /**
     * Shows a dialog with the generated text that can be copied by the user.
     *
     * @param text the text to display
     */
    private void showGeneratedTextDialog(String text) {
        JTextArea textArea = new JTextArea(20, 60);
        textArea.setText(text);
        textArea.setLineWrap(true);
        textArea.setWrapStyleWord(true);
        textArea.setEditable(false);

        JScrollPane scrollPane = new JScrollPane(textArea);
        scrollPane.setBorder(BorderFactory.createEmptyBorder(5, 5, 5, 5));

        JButton copyButton = new JButton("Copy to Clipboard & Open Github");
        copyButton.addActionListener(e -> {
            textArea.selectAll();
            textArea.copy();
            textArea.setSelectionStart(0);
            textArea.setSelectionEnd(0);

            try {
                Desktop.getDesktop().browse(URI.create(URL));
            } catch (IOException ignore) {
            }
        });

        JButton closeButton = new JButton("Close");
        closeButton.addActionListener(e -> SwingUtilities.getWindowAncestor(closeButton).dispose());

        JPanel buttonPanel = new JPanel(new FlowLayout(FlowLayout.RIGHT));
        buttonPanel.add(copyButton);
        buttonPanel.add(closeButton);

        JPanel contentPanel = new JPanel(new BorderLayout());
        contentPanel.add(scrollPane, BorderLayout.CENTER);
        contentPanel.add(buttonPanel, BorderLayout.SOUTH);

        JOptionPane pane =
            new JOptionPane(contentPanel, JOptionPane.PLAIN_MESSAGE, JOptionPane.NO_OPTION);
        JDialog dialog = pane.createDialog(mainWindow, "Generated GitHub Issue Text");
        dialog.setVisible(true);
    }
}
