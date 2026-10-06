/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.key.llm;

import java.awt.*;
import java.awt.event.InputEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;

import org.jspecify.annotations.Nullable;

/**
 * A text area with lightweight inline autocompletion:
 * <ul>
 * <li>{@code $} - context tokens (e.g. {@code $seq}, {@code $goals}, {@code $computePath})</li>
 * <li>{@code @} - files of the current Java model</li>
 * <li>{@code /} - skills and prompts from the user libraries</li>
 * </ul>
 * The popup follows the caret; Enter/Tab accept the selected entry, Up/Down navigate, Esc closes.
 *
 * @author Alexander Weigl
 */
public class AutocompleteInput extends JTextArea {

    /** A single completion proposal. */
    public record Suggestion(@Nullable String insert, String label, String detail,
            @Nullable Runnable action) {

        public Suggestion(String insert, String label, String detail) {
            this(insert, label, detail, null);
        }
    }

    /** Produces suggestions for a trigger character and the word typed so far. */
    public interface CompletionProvider {
        char trigger();

        List<Suggestion> apply(String prefix);
    }

    private final Map<Character, CompletionProvider> providers = new HashMap<>();
    private final JWindow popup = new JWindow();
    private final JList<Suggestion> list = new JList<>();
    private int completionStart = -1;
    private char activeTrigger;

    public AutocompleteInput() {
        setLineWrap(true);
        setWrapStyleWord(true);
        popup.setLayout(new BorderLayout());
        popup.add(new JScrollPane(list));
        popup.setSize(320, 150);

        list.setCellRenderer(new DefaultListCellRenderer() {
            @Override
            public Component getListCellRendererComponent(JList<?> l, Object value, int index,
                    boolean isSelected, boolean cellHasFocus) {
                var c = (JLabel) super.getListCellRendererComponent(l, value, index, isSelected,
                    cellHasFocus);
                if (value instanceof Suggestion s) {
                    c.setText("<html><b>" + s.label() + "</b> " + s.detail() + "</html>");
                }
                return c;
            }
        });

        list.addMouseListener(new MouseAdapter() {
            @Override
            public void mouseClicked(MouseEvent e) {
                if (e.getClickCount() == 2) {
                    accept();
                }
            }
        });

        getDocument().addDocumentListener(new DocumentListener() {
            @Override
            public void insertUpdate(DocumentEvent e) {
                updatePopup();
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                updatePopup();
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                updatePopup();
            }
        });

        addKeyListener(new KeyAdapter() {
            @Override
            public void keyPressed(KeyEvent e) {
                if (!popup.isVisible()) {
                    return;
                }
                int code = e.getKeyCode();
                // Ctrl/Cmd+Enter is the chat's send shortcut. It must never be consumed by the
                // completion popup, otherwise "/skills" (which always shows a suggestion) could
                // never actually be sent.
                final int modifiers =
                    InputEvent.CTRL_DOWN_MASK | InputEvent.META_DOWN_MASK
                            | InputEvent.ALT_DOWN_MASK;
                if (code == KeyEvent.VK_ENTER && (e.getModifiersEx() & modifiers) != 0) {
                    return;
                }
                if (code == KeyEvent.VK_UP) {
                    moveSelection(-1);
                    e.consume();
                } else if (code == KeyEvent.VK_DOWN) {
                    moveSelection(1);
                    e.consume();
                } else if (code == KeyEvent.VK_ENTER || code == KeyEvent.VK_TAB) {
                    accept();
                    e.consume();
                } else if (code == KeyEvent.VK_ESCAPE) {
                    popup.setVisible(false);
                    e.consume();
                }
            }
        });
    }

    public void addProvider(CompletionProvider provider) {
        providers.put(provider.trigger(), provider);
    }

    public List<Suggestion> suggestionsFor(char trigger, String prefix) {
        var provider = providers.get(trigger);
        return provider == null ? List.of() : provider.apply(prefix);
    }

    private void updatePopup() {
        if (providers.isEmpty()) {
            return;
        }
        computeCompletion();
        if (completionStart < 0) {
            popup.setVisible(false);
            return;
        }
        var state = gather();
        if (state.suggestions().isEmpty()) {
            popup.setVisible(false);
            return;
        }
        list.setListData(state.suggestions().toArray(new Suggestion[0]));
        var model = list.getModel();
        if (model.getSize() > 0) {
            list.setSelectedIndex(0);
        }
        positionPopup(state.caretOffset());
        popup.setVisible(true);
    }

    private record CompletionState(int caretOffset, List<Suggestion> suggestions) {
    }

    private CompletionState gather() {
        try {
            int caret = getCaretPosition();
            int line = getLineOfOffset(caret);
            int lineStart = getLineStartOffset(line);
            String prefix = getText(lineStart, caret - lineStart);
            // the word behind the trigger
            String word = prefix.substring(completionStart - lineStart + 1);
            var suggestions = suggestionsFor(activeTrigger, word);
            return new CompletionState(caret, suggestions);
        } catch (BadLocationException e) {
            return new CompletionState(-1, List.of());
        }
    }

    /**
     * Finds the trigger character that starts a completion at (or directly before) the caret, and
     * remembers its offset. A trigger only counts if the text between it and the caret is a
     * plausible word for the given trigger (letters, digits, '_' and '.').
     */
    private void computeCompletion() {
        completionStart = -1;
        try {
            int caret = getCaretPosition();
            if (caret == 0) {
                return;
            }
            String text = getText();
            int i = caret - 1;
            while (i >= 0) {
                char c = text.charAt(i);
                if (c == '$' || c == '@' || c == '/') {
                    String word = text.substring(i + 1, caret);
                    if (isPlausibleWord(c, word)) {
                        if (c == '/' && caret - i > 1 && word.contains(" ")) {
                            return; // a "/..." directive with a space must already have completed
                        }
                        completionStart = i;
                        activeTrigger = c;
                    }
                    return;
                }
                if (!isWordChar(c)) {
                    return;
                }
                i--;
            }
        } catch (Exception e) {
            completionStart = -1;
        }
    }

    private static boolean isPlausibleWord(char trigger, String word) {
        if (word.contains(" ")) {
            return trigger == '@' || trigger == '$';
        }
        return true;
    }

    private static boolean isWordChar(char c) {
        return Character.isLetterOrDigit(c) || c == '_' || c == '-' || c == '.' || c == ':';
    }

    private void positionPopup(int caretOffset) {
        try {
            var view = modelToView2D(caretOffset);
            Point loc = getLocationOnScreen();
            popup.setLocation(loc.x + (int) view.getX(), loc.y + (int) view.getY() + getFontMetrics(
                getFont()).getHeight() + 4);
        } catch (Exception e) {
            popup.setVisible(false);
        }
    }

    private void moveSelection(int delta) {
        int idx = list.getSelectedIndex();
        int next = Math.max(0, Math.min(list.getModel().getSize() - 1, idx + delta));
        list.setSelectedIndex(next);
        list.ensureIndexIsVisible(next);
    }

    private void accept() {
        Suggestion sel = list.getSelectedValue();
        if (sel == null) {
            popup.setVisible(false);
            return;
        }
        if (sel.action() != null) {
            popup.setVisible(false);
            sel.action().run();
            return;
        }
        if (sel.insert() != null) {
            try {
                getDocument().remove(completionStart, getCaretPosition() - completionStart);
                getDocument().insertString(completionStart, sel.insert(), null);
            } catch (BadLocationException e) {
                // ignore
            }
        }
        popup.setVisible(false);
    }
}
