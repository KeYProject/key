/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.GraphicsEnvironment;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.atomic.AtomicReference;
import javax.swing.SwingUtilities;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.proof.init.JavaProfile;

import org.key_project.util.java.SwingUtil;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Drives the real Ctrl+Space inline expansion in the real main window: a proof is loaded, the
 * KeY-Agent panel is docked (with the completion providers, the expand hook and the highlighters
 * of {@link LlmPrompt}), {@code $seq} is typed into the real input box and Ctrl+Space is
 * dispatched to it. The token must be replaced by the resolved sequent text, proving that the
 * shortcut reaches the expand hook in the production wiring (main-window key bindings, dock
 * structure, resolver) and is not swallowed by the AutoMode shortcut registered on the root pane.
 */
class LlmPromptExpandUiTest {

    @Test
    void ctrlSpaceReplacesTokenWithSequent() throws Exception {
        assumeTrue(!GraphicsEnvironment.isHeadless(),
            "requires a graphical environment (DISPLAY=" + System.getenv("DISPLAY") + ")");
        var tacletops = Path.of("src/test/resources/org/key_project/key/llm/tacletops.key");
        assumeTrue(Files.exists(tacletops), "File " + tacletops + " not found.");

        setWorkingDir(tacletops.toAbsolutePath().getParent());
        var env = WindowUserInterfaceControl.loadInMainWindow(JavaProfile.getDefaultInstance(),
            tacletops, List.of(), null, List.of(), false, false);
        var proof = env.getLoadedProof();
        assertNotNull(proof, "the test proof must be loaded");
        var main = MainWindow.getInstance();

        onEdt(() -> {
            main.getMediator().getSelectionModel().setSelectedNode(proof.root());
            DockingHelper.focus(main, LlmPrompt.class);
            main.setSize(1560, 1060);
            main.validate();
            return null;
        });

        var panel = SwingUtil.findComponent(main, LlmPrompt.class);
        assertNotNull(panel, "the KeY-Agent panel is not docked in the main window");
        var input = SwingUtil.findComponent(main, AutocompleteInput.class);
        assertNotNull(input, "the chat input box is not part of the main window");

        // type "$seq" character by character, like a user (this also opens the completion popup)
        type(input, "$seq");
        assertFalse(onEdt(input::getText).contains("==>"),
            "before expansion the input only contains the token");

        dispatchCtrlSpace(input);

        String text = onEdt(input::getText);
        assertTrue(text.contains("==>"), "Ctrl+Space must replace $seq by the sequent, got: "
            + text);
        assertFalse(text.contains("$seq"), "the $seq token must be gone after expansion");
    }

    private static void type(AutocompleteInput input, String text) throws Exception {
        onEdt(() -> {
            for (char c : text.toCharArray()) {
                input.replaceSelection(String.valueOf(c));
                input.setCaretPosition(input.getDocument().getLength());
            }
            return null;
        });
    }

    /** Dispatches a Ctrl+Space key press and release to the input, as the toolkit would. */
    private static void dispatchCtrlSpace(AutocompleteInput input) throws Exception {
        long when = System.currentTimeMillis();
        var press = new KeyEvent(input, KeyEvent.KEY_PRESSED, when, InputEvent.CTRL_DOWN_MASK,
            KeyEvent.VK_SPACE, KeyEvent.CHAR_UNDEFINED);
        var release = new KeyEvent(input, KeyEvent.KEY_RELEASED, when, InputEvent.CTRL_DOWN_MASK,
            KeyEvent.VK_SPACE, KeyEvent.CHAR_UNDEFINED);
        onEdt(() -> {
            input.dispatchEvent(press);
            input.dispatchEvent(release);
            return null;
        });
    }

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

    private static void setWorkingDir(Path dir) throws Exception {
        var field = Main.class.getDeclaredField("workingDir");
        field.setAccessible(true);
        field.set(null, dir);
    }
}
