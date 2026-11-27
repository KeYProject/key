/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.Component;
import java.awt.GraphicsEnvironment;
import java.awt.KeyboardFocusManager;
import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;
import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.KeyStroke;
import javax.swing.SwingUtilities;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Regression test for the Ctrl+Enter send shortcut of the KeY-Agent chat panel: the send action
 * must fire when the keyboard focus is on the {@link AutocompleteInput} itself (completion popup
 * closed or open) as well as when the focus is on another part of the {@link LlmPrompt} panel,
 * while it must not fire when the focus is outside the panel.
 * <p>
 * The test drives the real Swing key dispatch (window, focus manager and key bindings), so it
 * needs a display and is skipped in headless environments. {@link LlmPrompt} cannot be
 * instantiated without a running KeY, so the bindings are wired exactly as in {@link LlmPrompt}
 * onto a real {@link AutocompleteInput}.
 */
class SendBindingUiTest {

    /** The text sent through the "sendPrompt" action, or {@code null} if it never fired. */
    private final AtomicReference<String> sent = new AtomicReference<>();

    @Test
    void ctrlEnterSendsWhenInputHasFocus() {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "needs a display");
        var panel = new JPanel();
        var input = new AutocompleteInput();
        panel.add(new JScrollPane(input));
        bindSend(input);
        try (var frame = new TestFrame(panel)) {
            frame.showAndFocus(input);
            assertTrue(focused(input), "the input should have the keyboard focus");
            type(input, "hello agent");
            typeCtrlEnter(input);
            assertEquals("hello agent", sent.get(), "Ctrl+Enter must fire the send action");
        }
    }

    @Test
    void ctrlEnterSendsWhileCompletionPopupIsOpen() {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "needs a display");
        var panel = new JPanel();
        var input = new AutocompleteInput();
        input.addProvider(new AutocompleteInput.CompletionProvider() {
            @Override
            public char trigger() {
                return '/';
            }

            @Override
            public List<AutocompleteInput.Suggestion> apply(String prefix) {
                return prefix.isEmpty() || "skills".startsWith(prefix)
                        ? List.of(new AutocompleteInput.Suggestion("/skills ", "/skills",
                            "list the skills"))
                        : List.of();
            }
        });
        panel.add(new JScrollPane(input));
        bindSend(input);
        try (var frame = new TestFrame(panel)) {
            frame.showAndFocus(input);
            assertTrue(focused(input), "the input should have the keyboard focus");
            // open the completion popup by typing the "/skill" directive, as the chat panel
            // users do (a bulk setText would fire the document update with a stale caret)
            type(input, "/skill");
            awaitPopup(input);
            typeCtrlEnter(input);
            assertEquals("/skill", sent.get(), "Ctrl+Enter must send, not accept the completion");
            assertEquals("/skill", onEdt(input::getText), "the completion must not be accepted");
        }
    }

    @Test
    void ctrlEnterSendsWhenFocusIsOnAnotherPartOfThePanel() {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "needs a display");
        var panel = new JPanel();
        var input = new AutocompleteInput();
        var button = new JButton("Stop");
        panel.add(new JScrollPane(input));
        panel.add(button);
        bindSend(input);
        bindPanelSend(panel, input);
        try (var frame = new TestFrame(panel)) {
            frame.showAndFocus(button);
            assertTrue(focused(button), "the button should have the keyboard focus");
            type(input, "hello agent");
            typeCtrlEnter(button);
            assertEquals("hello agent", sent.get(),
                "Ctrl+Enter must fire even when the focus is on a sibling of the input");
        }
    }

    @Test
    void ctrlEnterDoesNotSendWhenFocusIsOutsideThePanel() {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "needs a display");
        var panel = new JPanel();
        var input = new AutocompleteInput();
        panel.add(new JScrollPane(input));
        bindSend(input);
        bindPanelSend(panel, input);
        var outside = new JButton("elsewhere");
        var frame = new TestFrame(panel);
        try {
            onEdt(() -> {
                frame.content().add(outside);
                frame.content().validate();
                return null;
            });
            frame.showAndFocus(outside);
            assertTrue(focused(outside), "the outside button should have the keyboard focus");
            type(input, "hello agent");
            typeCtrlEnter(outside);
            assertNull(sent.get(),
                "Ctrl+Enter must not send while the focus is outside the chat panel");
        } finally {
            frame.close();
        }
    }

    /** The input binding as installed by {@link LlmPrompt}: Ctrl+Enter fires "sendPrompt". */
    private void bindSend(AutocompleteInput input) {
        input.getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_ENTER,
            InputEvent.CTRL_DOWN_MASK), "sendPrompt");
        input.getActionMap().put("sendPrompt", record(input));
    }

    /** The panel binding as installed by {@link LlmPrompt} next to the input binding. */
    private void bindPanelSend(JPanel panel, AutocompleteInput input) {
        panel.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).put(
            KeyStroke.getKeyStroke(KeyEvent.VK_ENTER, InputEvent.CTRL_DOWN_MASK), "sendPrompt");
        panel.getActionMap().put("sendPrompt", record(input));
    }

    private AbstractAction record(AutocompleteInput input) {
        return new AbstractAction() {
            @Override
            public void actionPerformed(ActionEvent e) {
                sent.set(input.getText());
            }
        };
    }

    /**
     * Simulates the user pressing Ctrl+Enter while {@code focusOwner} has the keyboard focus: on
     * the EDT, the key events are dispatched to the focus owner (as the real event queue would)
     * and may then propagate to the ancestors, exactly like a real key press.
     */
    private void typeCtrlEnter(Component focusOwner) {
        long when = System.currentTimeMillis();
        var press = new KeyEvent(focusOwner, KeyEvent.KEY_PRESSED, when, InputEvent.CTRL_DOWN_MASK,
            KeyEvent.VK_ENTER, KeyEvent.CHAR_UNDEFINED);
        var release =
            new KeyEvent(focusOwner, KeyEvent.KEY_RELEASED, when, InputEvent.CTRL_DOWN_MASK,
                KeyEvent.VK_ENTER, KeyEvent.CHAR_UNDEFINED);
        onEdt(() -> {
            focusOwner.dispatchEvent(press);
            focusOwner.dispatchEvent(release);
            return null;
        });
        // let any pending EDT work settle before asserting
        onEdt(() -> null);
    }

    /** Types the text character by character at the caret, like a user would. */
    private static void type(AutocompleteInput input, String text) {
        onEdt(() -> {
            for (char c : text.toCharArray()) {
                input.replaceSelection(String.valueOf(c));
                input.setCaretPosition(input.getDocument().getLength());
            }
            return null;
        });
    }

    private static boolean focused(Component c) {
        return KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner() == c;
    }

    private static <T> T onEdt(Supplier<T> r) {
        var result = new AtomicReference<T>();
        try {
            SwingUtilities.invokeAndWait(() -> result.set(r.get()));
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException(e);
        }
        return result.get();
    }

    private static void awaitPopup(AutocompleteInput input) {
        long deadline = System.currentTimeMillis() + 5000;
        while (!input.isPopupVisible() && System.currentTimeMillis() < deadline) {
            try {
                Thread.sleep(20);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return;
            }
        }
        assertTrue(input.isPopupVisible(), "the completion popup should be open");
    }

    /** A frame holding the given root; shows it and moves the keyboard focus to a component. */
    private final class TestFrame implements AutoCloseable {
        private final JFrame frame = new JFrame("send binding test");

        TestFrame(JComponent root) {
            frame.add(root);
            frame.setSize(420, 200);
            frame.setLocationByPlatform(true);
        }

        JComponent content() {
            return (JComponent) frame.getContentPane();
        }

        void showAndFocus(Component target) {
            onEdt(() -> {
                frame.setVisible(true);
                target.requestFocusInWindow();
                return null;
            });
            long deadline = System.currentTimeMillis() + 5000;
            while (!focused(target) && System.currentTimeMillis() < deadline) {
                try {
                    Thread.sleep(20);
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    return;
                }
            }
        }

        @Override
        public void close() {
            onEdt(() -> {
                frame.dispose();
                return null;
            });
        }
    }
}
