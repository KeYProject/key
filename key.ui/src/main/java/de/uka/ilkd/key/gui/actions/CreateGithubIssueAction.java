/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URLEncoder;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.FontAwesomeBrands;
import de.uka.ilkd.key.gui.fonticons.IconFontProvider;
import de.uka.ilkd.key.gui.fonticons.IconProvider;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.OutputStreamProofSaver;
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
            File javaSourceLocation = OutputStreamProofSaver.getJavaSourceLocation(proof);
            if (javaSourceLocation != null) {
                Path path = javaSourceLocation.toPath();
                try (final var walker = Files.walk(path)) {
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
            LOGGER.error("Could not open browser for URI {}.", uri, e);
        }

    }
}
