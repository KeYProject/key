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
import java.util.concurrent.atomic.AtomicInteger;
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
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * Regression test for the Ctrl+Space inline expansion of {@code $tokens} in the input widget, in
 * the exact wiring of {@link LlmPrompt}: the input's key listener handles the shortcut while the
 * input has the focus (the listener consumes the event before any key binding), and a panel-level
 * {@code WHEN_ANCESTOR_OF_FOCUSED_COMPONENT} binding covers the rest of the panel. The root-pane
 * AutoMode binding for Ctrl+Space (as registered by {@code MainWindow}) must never win while the
 * focus is inside the chat panel.
 */
class ExpandBindingUiTest {

    /** The text substituted for {@code $seq} by the test resolver. */
    private static final String EXPANDED = "1 ::= true";

    private final AtomicInteger autoModeFired = new AtomicInteger();
    private final AtomicInteger expandFired = new AtomicInteger();

    private final AutocompleteInput input = new AutocompleteInput();
    private final JPanel panel = new JPanel();
    private final JButton sibling = new JButton("Stop");
    private final JButton outside = new JButton("elsewhere");

    private void setUpPanel() {
        input.addProvider(autocompleteProvider());
        panel.add(new JScrollPane(input));
        panel.add(sibling);
        bindExpand();
    }

    /** The expand wiring as installed by {@link LlmPrompt}. */
    private void bindExpand() {
        var stroke = KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, InputEvent.CTRL_DOWN_MASK);
        var action = new AbstractAction() {
            @Override
            public void actionPerformed(ActionEvent e) {
                expand();
            }
        };
        input.setExpandHook(this::expand);
        input.getInputMap().put(stroke, "expandAtCaret");
        input.getActionMap().put("expandAtCaret", action);
        panel.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT).put(stroke,
            "expandAtCaret");
        panel.getActionMap().put("expandAtCaret", action);
    }

    /** Replaces the {@code $seq} at the caret with the expanded value. */
    private void expand() {
        boolean ok = input.expandAtCaret(fragment -> fragment.equals("$seq") ? EXPANDED : null);
        if (ok) {
            expandFired.incrementAndGet();
        }
    }

    @Test
    void ctrlSpaceExpandsWhenInputHasFocus() {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "needs a display");
        setUpPanel();
        try (var frame = new TestFrame(panel)) {
            frame.bindRootPaneCtrlSpace(() -> autoModeFired.incrementAndGet());
            frame.showAndFocus(input);
            assertTrue(focused(input), "the input should have the keyboard focus");
            type(input, "$seq");
            typeCtrlSpace(input);
            assertEquals(EXPANDED, onEdt(input::getText),
                "Ctrl+Space must expand the $token at the caret");
            assertEquals(1, expandFired.get());
            assertEquals(0, autoModeFired.get(),
                "the root-pane AutoMode binding must not swallow Ctrl+Space");
        }
    }

    @Test
    void ctrlSpaceExpandsWhenFocusIsOnASiblingInThePanel() {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "needs a display");
        setUpPanel();
        try (var frame = new TestFrame(panel)) {
            frame.bindRootPaneCtrlSpace(() -> autoModeFired.incrementAndGet());
            frame.showAndFocus(sibling);
            assertTrue(focused(sibling), "the sibling should have the keyboard focus");
            type(input, "$seq");
            typeCtrlSpace(sibling);
            assertEquals(EXPANDED, onEdt(input::getText),
                "the panel-level binding must expand even when the focus is not on the input");
            assertEquals(1, expandFired.get());
            assertEquals(0, autoModeFired.get(),
                "the panel binding must win over the root-pane AutoMode binding");
        }
    }

    @Test
    void ctrlSpaceDoesNotExpandWhenFocusIsOutsideThePanel() {
        assumeTrue(!GraphicsEnvironment.isHeadless(), "needs a display");
        setUpPanel();
        var frame = new TestFrame(panel);
        try {
            onEdt(() -> {
                frame.content().add(outside);
                frame.content().validate();
                return null;
            });
            frame.bindRootPaneCtrlSpace(() -> autoModeFired.incrementAndGet());
            frame.showAndFocus(outside);
            assertTrue(focused(outside), "the outside button should have the keyboard focus");
            type(input, "$seq");
            typeCtrlSpace(outside);
            assertEquals("$seq", onEdt(input::getText),
                "the expansion must not fire while the focus is outside the chat panel");
            assertEquals(0, expandFired.get());
            assertEquals(1, autoModeFired.get(),
                "outside the panel Ctrl+Space is the AutoMode shortcut");
        } finally {
            frame.close();
        }
    }

    /** A {@code $} provider as in {@link AutocompleteProviders#contextTokens()}. */
    private static AutocompleteInput.CompletionProvider autocompleteProvider() {
        return new AutocompleteInput.CompletionProvider() {
            @Override
            public char trigger() {
                return '$';
            }

            @Override
            public List<AutocompleteInput.Suggestion> apply(String prefix) {
                return prefix.isEmpty() || "seq".startsWith(prefix)
                        ? List.of(new AutocompleteInput.Suggestion("$seq ", "$seq",
                            "the current sequent"))
                        : List.of();
            }
        };
    }

    /** Simulates the user pressing Ctrl+Space while {@code focusOwner} holds the focus. */
    private void typeCtrlSpace(Component focusOwner) {
        long when = System.currentTimeMillis();
        var press = new KeyEvent(focusOwner, KeyEvent.KEY_PRESSED, when, InputEvent.CTRL_DOWN_MASK,
            KeyEvent.VK_SPACE, KeyEvent.CHAR_UNDEFINED);
        var release =
            new KeyEvent(focusOwner, KeyEvent.KEY_RELEASED, when, InputEvent.CTRL_DOWN_MASK,
                KeyEvent.VK_SPACE, KeyEvent.CHAR_UNDEFINED);
        onEdt(() -> {
            focusOwner.dispatchEvent(press);
            focusOwner.dispatchEvent(release);
            return null;
        });
        // let any pending EDT work settle before asserting
        onEdt(() -> null);
    }

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
        var result = new java.util.concurrent.atomic.AtomicReference<T>();
        try {
            SwingUtilities.invokeAndWait(() -> result.set(r.get()));
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        } catch (java.lang.reflect.InvocationTargetException e) {
            throw new RuntimeException(e);
        }
        return result.get();
    }

    /** A frame with a root pane; the Ctrl+Space binding mirrors {@code MainWindow}. */
    private final class TestFrame implements AutoCloseable {
        private final JFrame frame = new JFrame("expand binding test");

        TestFrame(JComponent root) {
            frame.add(root);
            frame.setSize(420, 220);
            frame.setLocationByPlatform(true);
        }

        JComponent content() {
            return (JComponent) frame.getContentPane();
        }

        void bindRootPaneCtrlSpace(Runnable action) {
            var stroke = KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, InputEvent.CTRL_DOWN_MASK);
            frame.getRootPane().getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT)
                    .put(stroke, "defaultAutomation");
            frame.getRootPane().getActionMap().put("defaultAutomation", new AbstractAction() {
                @Override
                public void actionPerformed(ActionEvent e) {
                    action.run();
                }
            });
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
