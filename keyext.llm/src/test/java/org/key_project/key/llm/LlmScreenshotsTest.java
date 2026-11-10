/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.Component;
import java.awt.GraphicsEnvironment;
import java.awt.RenderingHints;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.atomic.AtomicReference;
import javax.imageio.ImageIO;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.settings.SettingsDialog;
import de.uka.ilkd.key.gui.settings.SettingsManager;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.gui.settings.SettingsUi;
import de.uka.ilkd.key.proof.init.JavaProfile;

import org.key_project.util.java.SwingUtil;

import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Renders the user-facing screenshots of the KeY-Agent chat panel and of its settings panels by
 * painting the Swing components into {@link BufferedImage}s (no screen capture is involved):
 * <ul>
 * <li>{@code llm-panel.png}: the main window with the panel docked at the right and a seeded
 * conversation (prompt, tool activity, answer);</li>
 * <li>{@code llm-markdown.png}: close-up of the chat panel with the Markdown-rendered answer;</li>
 * <li>{@code llm-settings.png}: the settings dialog on the "LLM Settings" node;</li>
 * <li>{@code llm-settings-tools.png}: the settings dialog on the "Tools" node.</li>
 * </ul>
 * The images are written to {@code build/screenshot} and are meant to be copied into the
 * documentation. Neither the main window nor the settings dialog is ever shown on the display;
 * the JVM still requires a graphical environment because constructing the {@link MainWindow}
 * terminates in headless mode.
 */
class LlmScreenshotsTest {
    private static final Logger LOGGER = LoggerFactory.getLogger(LlmScreenshotsTest.class);

    /** Width and height of the painted main window. */
    private static final int W = 1560;
    private static final int H = 1060;

    @Test
    void capture() throws Exception {
        LOGGER.info("DISPLAY={} headless={}", System.getenv("DISPLAY"),
            GraphicsEnvironment.isHeadless());
        assumeTrue(!GraphicsEnvironment.isHeadless(),
            "requires a graphical environment (DISPLAY=" + System.getenv("DISPLAY") + ")");
        var tacletops = Path.of("src/test/resources/org/key_project/key/llm/tacletops.key");
        assumeTrue(Files.exists(tacletops), "File " + tacletops + " not found.");

        // realistic-looking connection details; the settings panels copy the model when they are
        // created, which happens while the dialog is built below
        LlmSettings.INSTANCE.setAuthToken("your-auth-token");

        // Main.main would normally derive the working directory from the command line
        setWorkingDir(tacletops.toAbsolutePath().getParent());
        // the last argument keeps the main window hidden: everything is painted off-screen
        var env = WindowUserInterfaceControl.loadInMainWindow(JavaProfile.getDefaultInstance(),
            tacletops, List.of(), null, List.of(), false, false);
        var proof = env.getLoadedProof();
        assertNotNull(proof, "the test proof must be loaded");
        var main = MainWindow.getInstance();

        var panel = SwingUtil.findComponent(main, LlmPrompt.class);
        assertNotNull(panel, "the KeY-Agent panel is not docked in the main window");

        // deterministic layout: select the proof's root node (so that the sequent view shows a
        // goal), show the panel's tab and give the window a fixed size
        onEdt(() -> {
            main.getMediator().getSelectionModel().setSelectedNode(proof.root());
            DockingHelper.focus(main, LlmPrompt.class);
            main.setSize(W, H);
            main.validate();
            return null;
        });

        // a short scripted conversation: prompt, tool activity, answer
        onEdt(() -> {
            panel.addInput("Which taclets can I use on the current goal?");
            panel.addToolActivities(List.of(
                new AgentResult.ToolActivity("list_taclets", "{}",
                    "available taclets: auto, auto_ind, seq, seq_ind, ..."),
                new AgentResult.ToolActivity("get_proof_context", "{}",
                    "proof 'tacletops' with one open goal: x > 0")));
            panel.addOutput(
                """
                        For this goal the taclets `auto`, `seq` and `auto_ind` look promising. I recommend \
                        trying `auto` first: it applies a set of standard rules and closes the goal \
                        directly.

                        **Suggested steps:**

                        1. apply `auto` on the open goal
                        2. if it does not close, apply `seq` to split the implication
                        3. run `auto_ind` on the remaining subgoal

                        ```key
                        auto;
                        seq;
                        ```

                        | Taclet     | Effect                        |
                        | ---------- | ----------------------------- |
                        | `auto`     | closes trivial goals directly |
                        | `seq`      | splits the implication        |
                        | `auto_ind` | applies induction heuristics  |

                        See [taclets](https://key-project.org) for details.
                        """);
            return null;
        });
        onEdt(() -> {
            main.validate();
            return null;
        });

        var out = Path.of("build", "screenshot");
        Files.createDirectories(out);

        // the main window: menu bar, proof views and the docked chat panel
        onEdt(() -> {
            // a second pass lets the conversation layout settle (the preferred width of the
            // Markdown boxes depends on the viewport width, which depends on the scrollbars,
            // which depend on the preferred widths)
            main.validate();
            write(main.getRootPane(), out.resolve("llm-panel.png"));
            return null;
        });

        // close-up of the chat panel: the Markdown-rendered answer
        onEdt(() -> {
            main.validate();
            write(panel, out.resolve("llm-markdown.png"));
            return null;
        });

        var dialog = onEdt(() -> buildSettingsDialog(main));
        try {
            onEdt(() -> {
                select(dialog, LlmExtension.LlmSettingsProvider.INSTANCE);
                dialog.validate();
                return null;
            });
            onEdt(() -> {
                write(dialog.getRootPane(), out.resolve("llm-settings.png"));
                return null;
            });

            onEdt(() -> {
                select(dialog, LlmExtension.LlmSettingsProvider.TOOLS);
                dialog.validate();
                return null;
            });
            onEdt(() -> {
                write(dialog.getRootPane(), out.resolve("llm-settings-tools.png"));
                return null;
            });
        } finally {
            onEdt(() -> {
                dialog.dispose();
                return null;
            });
        }
    }

    /**
     * Builds the settings dialog off-screen, the same way
     * {@link SettingsManager#showSettingsDialog(MainWindow, SettingsProvider)} does (all
     * registered providers, dialog sized accordingly), minus showing it.
     */
    private static SettingsDialog buildSettingsDialog(MainWindow main) throws Exception {
        var manager = SettingsManager.getInstance();
        var field = SettingsManager.class.getDeclaredField("settingsProviders");
        field.setAccessible(true);
        var providers = (List<SettingsProvider>) field.get(manager);
        var dialog = new SettingsDialog(main);
        dialog.setSettingsProvider(providers);
        return dialog;
    }

    /** Selects the given settings node; the dialog's UI accessor is package-private. */
    private static void select(SettingsDialog dialog, SettingsProvider node) throws Exception {
        var getUi = SettingsDialog.class.getDeclaredMethod("getUi");
        getUi.setAccessible(true);
        ((SettingsUi) getUi.invoke(dialog)).selectPanel(node);
    }

    /**
     * Runs the given work on the event dispatch thread, rethrowing any exception it throws.
     */
    private static <T> T onEdt(Callable<T> work) throws Exception {
        var result = new AtomicReference<T>();
        var error = new AtomicReference<Throwable>();
        SwingUtilities.invokeAndWait(() -> {
            try {
                result.set(work.call());
            } catch (Throwable t) {
                error.set(t);
            }
        });
        if (error.get() != null) {
            throw (error.get() instanceof Exception e) ? e : new RuntimeException(error.get());
        }
        return result.get();
    }


    /**
     * Paints the component (which must be sized and validated) into a new image and writes it as
     * PNG.
     */
    private static void write(Component c, Path file) throws IOException {
        var image = new BufferedImage(c.getWidth(), c.getHeight(), BufferedImage.TYPE_INT_RGB);
        var g = image.createGraphics();
        try {
            g.setRenderingHint(RenderingHints.KEY_TEXT_ANTIALIASING,
                RenderingHints.VALUE_TEXT_ANTIALIAS_ON);
            g.setColor(c.getBackground());
            g.fillRect(0, 0, image.getWidth(), image.getHeight());
            c.paint(g);
        } finally {
            g.dispose();
        }
        ImageIO.write(image, "png", file.toFile());
        LOGGER.info("wrote {} ({}x{})", file, image.getWidth(), image.getHeight());
    }

    /**
     * Sets the {@link Main} working directory, which {@code Main.main} would normally derive from
     * the command line arguments before the main window is constructed.
     */
    private static void setWorkingDir(Path dir) throws Exception {
        var field = Main.class.getDeclaredField("workingDir");
        field.setAccessible(true);
        field.set(null, dir);
    }
}
