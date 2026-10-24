/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.llm;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Cursor;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.Point;
import java.awt.Rectangle;
import java.awt.Toolkit;
import java.awt.datatransfer.DataFlavor;
import java.awt.datatransfer.StringSelection;
import java.awt.datatransfer.Transferable;
import java.awt.event.InputEvent;
import java.awt.event.KeyAdapter;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseMotionAdapter;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.regex.Pattern;
import javax.swing.*;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultStyledDocument;
import javax.swing.text.JTextComponent;
import javax.swing.text.MutableAttributeSet;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;

import de.uka.ilkd.key.gui.utilities.LexerHighlighter;

import org.jspecify.annotations.Nullable;

/**
 * The prompt input box with lightweight inline autocompletion:
 * <ul>
 * <li>{@code $} - context tokens (e.g. {@code $seq}, {@code $goals}, {@code $computePath})</li>
 * <li>{@code @} - files of the current Java model</li>
 * <li>{@code /} - skills and prompts from the user libraries</li>
 * </ul>
 * The popup follows the caret; Enter/Tab accept the selected entry, Up/Down navigate, Esc closes.
 * It can be resized by dragging the handle in its bottom-right corner; without resizing it fits
 * the content and the width of the input box.
 * <p>
 * Terms and sequents dragged in from the sequent view are inserted wrapped in verbatim marks:
 * inline backticks for single-line content, a fenced block with the {@code key} language marker
 * for multi-line content. When a {@link LexerHighlighter} is set (see
 * {@link #setHighlighter(LexerHighlighter)}), {@code ```key} fences are highlighted with the KeY
 * lexer.
 *
 * @author Alexander Weigl
 */
public class AutocompleteInput extends JTextPane {

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
    private final ResizeGrip resizeGrip = new ResizeGrip();
    private int completionStart = -1;
    private char activeTrigger;

    /** The highlighter for {@code ```key} fences (or {@code null}). */
    private @Nullable LexerHighlighter highlighter;
    private boolean highlightScheduled;

    /** Popup size chosen by the user with the resize grip; kept on re-show. */
    private int userPopupWidth;
    private int userPopupHeight;

    /**
     * Suppresses popup and highlight updates while the component itself modifies the document
     * (completing, expanding, dropping): the document listeners would otherwise recompute the
     * completion state in the middle of the modification.
     */
    private boolean suspendUpdates;
    /**
     * Set when Enter/Tab confirmed a completion: the following KEY_TYPED event of that key would
     * insert a line break or tab into the text.
     */
    private boolean suppressTypedKey;

    /** Invoked when the user presses Ctrl+Space; set by the chat panel. */
    private @Nullable Runnable expandHook;

    /** Smallest allowed popup size when the user resizes it with the grip. */
    private static final int MIN_POPUP_WIDTH = 120;
    private static final int MIN_POPUP_HEIGHT = 80;
    /** Largest height the popup grows to on its own; the grip can exceed it. */
    private static final int MAX_AUTO_POPUP_HEIGHT = 320;
    /** Margin added around the popup content. */
    private static final int POPUP_MARGIN = 24;

    public AutocompleteInput() {
        popup.setLayout(new BorderLayout());
        popup.add(new JScrollPane(list), BorderLayout.CENTER);
        var bottom = new JPanel(new BorderLayout());
        bottom.setOpaque(false);
        bottom.add(resizeGrip, BorderLayout.EAST);
        popup.add(bottom, BorderLayout.SOUTH);
        popup.setSize(320, 150);
        // Clicks in the popup must not steal the keyboard focus: the user may select an entry and
        // then continue typing or press Enter to confirm the completion.
        popup.setFocusableWindowState(false);
        list.setFocusable(false);

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
                if (e.getButton() != MouseEvent.BUTTON1) {
                    return;
                }
                int idx = list.locationToIndex(e.getPoint());
                Rectangle cell = idx < 0 ? null : list.getCellBounds(idx, idx);
                if (cell == null || !cell.contains(e.getPoint())) {
                    // click on empty area closes the popup
                    popup.setVisible(false);
                    return;
                }
                list.setSelectedIndex(idx);
                accept();
            }
        });

        getDocument().addDocumentListener(new DocumentListener() {
            private void changed(boolean attributeOnly) {
                if (suspendUpdates) {
                    return;
                }
                updatePopup();
                if (!attributeOnly) {
                    scheduleHighlight();
                }
            }

            @Override
            public void insertUpdate(DocumentEvent e) {
                changed(false);
            }

            @Override
            public void removeUpdate(DocumentEvent e) {
                changed(false);
            }

            @Override
            public void changedUpdate(DocumentEvent e) {
                // attribute-only changes (e.g. from the highlighter) must not re-highlight
                changed(true);
            }
        });

        addKeyListener(new KeyAdapter() {
            @Override
            public void keyPressed(KeyEvent e) {
                suppressTypedKey = false;
                // Ctrl+Space expands the $token / @file / /directive at the caret (the chat
                // panel registers the hook). Handled directly in the key listener so that no
                // key binding of the component or an ancestor can swallow the shortcut.
                if (e.getKeyCode() == KeyEvent.VK_SPACE
                        && (e.getModifiersEx() & InputEvent.CTRL_DOWN_MASK) != 0) {
                    e.consume();
                    if (expandHook != null) {
                        expandHook.run();
                    }
                    return;
                }
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
                    // the KEY_TYPED event of the confirmed key would insert a line break or tab
                    suppressTypedKey = true;
                    e.consume();
                } else if (code == KeyEvent.VK_ESCAPE) {
                    popup.setVisible(false);
                    e.consume();
                }
            }

            @Override
            public void keyTyped(KeyEvent e) {
                if (suppressTypedKey) {
                    suppressTypedKey = false;
                    if (e.getKeyChar() == '\n' || e.getKeyChar() == '\t') {
                        e.consume();
                    }
                }
            }
        });

        installDropHandler();
    }

    // ----------------------------------------------------------------------- configuration

    public void addProvider(CompletionProvider provider) {
        providers.put(provider.trigger(), provider);
    }

    /**
     * Sets the highlighter for {@code ```key} fences in the input (or {@code null} to disable).
     * The fences are highlighted with the KeY lexer on every text change.
     */
    public void setHighlighter(@Nullable LexerHighlighter highlighter) {
        this.highlighter = highlighter;
        scheduleHighlight();
    }

    /**
     * Sets the hook that is invoked when the user presses Ctrl+Space (the chat panel uses it to
     * expand the {@code $token}/{@code @file}/{@code /directive} at the caret). The hook runs
     * directly from the key listener, before any key binding processing.
     */
    public void setExpandHook(@Nullable Runnable expandHook) {
        this.expandHook = expandHook;
    }

    public List<Suggestion> suggestionsFor(char trigger, String prefix) {
        var provider = providers.get(trigger);
        return provider == null ? List.of() : provider.apply(prefix);
    }

    // ---------------------------------------------------------------------------- dropping

    /**
     * Wraps dropped content into verbatim marks: single-line text in inline backticks, multi-line
     * text in a fenced block with the KeY language marker.
     */
    public static String verbatim(String text) {
        var stripped = text.strip();
        return stripped.contains("\n")
                ? "```key\n" + stripped + "\n```"
                : "`" + stripped + "`";
    }

    /**
     * Installs a drop handler that inserts dropped terms/sequents wrapped in verbatim marks
     * ({@link #verbatim(String)}). Paste inserts plain text at the caret, cut and copy act on the
     * current selection, as usual for text components.
     */
    private void installDropHandler() {
        setTransferHandler(new TransferHandler() {
            @Override
            public boolean canImport(TransferSupport support) {
                return support.isDrop() && support.isDataFlavorSupported(DataFlavor.stringFlavor);
            }

            @Override
            public boolean importData(TransferSupport support) {
                if (!canImport(support)) {
                    return false;
                }
                try {
                    var data = (String) support.getTransferable()
                            .getTransferData(DataFlavor.stringFlavor);
                    if (data == null || data.isBlank()) {
                        return false;
                    }
                    int index =
                        ((JTextComponent.DropLocation) support.getDropLocation()).getIndex();
                    insertWrapped(index, data);
                    return true;
                } catch (Exception e) {
                    return false;
                }
            }

            // --- clipboard actions (paste / cut / copy) ---

            @Override
            public boolean importData(JComponent comp, Transferable t) {
                try {
                    var data = (String) t.getTransferData(DataFlavor.stringFlavor);
                    if (data == null) {
                        return false;
                    }
                    replaceSelection(data);
                    return true;
                } catch (Exception e) {
                    return false;
                }
            }

            @Override
            public Transferable createTransferable(JComponent c) {
                String selection = getSelectedText();
                return selection == null ? null : new StringSelection(selection);
            }

            @Override
            public int getSourceActions(JComponent c) {
                return COPY_OR_MOVE;
            }

            @Override
            public void exportDone(JComponent source, Transferable data, int action) {
                if (action == MOVE) {
                    // cut: the exported selection is removed afterwards
                    replaceSelection("");
                }
            }
        });
    }

    /** Inserts {@code data} verbatim-wrapped at {@code index}, surrounded by separating spaces. */
    private void insertWrapped(int index, String data) {
        var current = getText();
        boolean spaceBefore = index > 0 && !Character.isWhitespace(current.charAt(index - 1));
        boolean spaceAfter = index < current.length()
                && !Character.isWhitespace(current.charAt(index));
        var wrapped = (spaceBefore ? " " : "") + verbatim(data) + (spaceAfter ? " " : "");
        try {
            suspendUpdates = true;
            try {
                getDocument().insertString(index, wrapped, null);
            } finally {
                suspendUpdates = false;
            }
            setCaretPosition(index + wrapped.length());
        } catch (BadLocationException e) {
            getToolkit().beep();
        }
    }

    // -------------------------------------------------------------------------- highlighting

    /**
     * Re-highlights the {@code ```key} fences (scheduled; never during a document notification).
     */
    private void scheduleHighlight() {
        if (highlighter == null || highlightScheduled) {
            return;
        }
        highlightScheduled = true;
        SwingUtilities.invokeLater(() -> {
            highlightScheduled = false;
            applyHighlight();
        });
    }

    private void applyHighlight() {
        var highlighter = this.highlighter;
        if (highlighter == null) {
            return;
        }
        try {
            var document = (DefaultStyledDocument) getDocument();
            // reset the whole document to the plain default style first, so that typed text does
            // not keep the token colors of its neighborhood, then re-apply the token styles
            document.setCharacterAttributes(0, document.getLength(), defaultAttributes(), true);
            highlighter.highlightPaneMarkdown(this);
        } catch (RuntimeException e) {
            // highlighting is best-effort
        }
    }

    /** The plain attributes matching this component's default font and foreground. */
    private MutableAttributeSet defaultAttributes() {
        var font = getFont();
        var set = new SimpleAttributeSet();
        StyleConstants.setFontFamily(set, font.getFamily());
        StyleConstants.setFontSize(set, font.getSize());
        StyleConstants.setForeground(set, getForeground());
        StyleConstants.setBold(set, false);
        StyleConstants.setItalic(set, false);
        return set;
    }

    // ------------------------------------------------------------------------ completions

    /**
     * The {@code $token}, {@code @file} or {@code /directive} fragment directly before the caret
     * (e.g. {@code $seq}, {@code @src/Main.java}, {@code /skills}), or {@code null} if the caret is
     * not immediately after such a fragment.
     */
    public @Nullable String tokenAtCaret() {
        return tokenFragmentAtCaret(getText(), getCaretPosition());
    }

    private static final Pattern EXPANDABLE = Pattern
            .compile("(\\$[\\p{Alnum}_]+|@[\\p{Alnum}_.\\-/]+|/(?:skills|prompts"
                + "|skill:[\\p{Alnum}_-]+|prompt:[\\p{Alnum}_-]+))$");

    static @Nullable String tokenFragmentAtCaret(String text, int caret) {
        if (text == null || caret <= 0 || caret > text.length()) {
            return null;
        }
        var head = text.substring(0, caret);
        var matcher = EXPANDABLE.matcher(head);
        if (!matcher.find()) {
            return null;
        }
        int start = matcher.start();
        // the fragment must not be the tail of a larger word
        if (start > 0 && Character.isLetterOrDigit(head.charAt(start - 1))) {
            return null;
        }
        return matcher.group();
    }

    /**
     * Replaces the {@code $token}/{@code @file}/{@code /directive} fragment before the caret by
     * its expanded content and moves the caret to the end of the inserted text. A fragment that
     * cannot be resolved (resolver returns {@code null} or blank text) is left untouched and the
     * toolkit beeps.
     */
    public void expandAtCaret(Function<String, @Nullable String> resolver) {
        String fragment = tokenAtCaret();
        if (fragment == null) {
            getToolkit().beep();
            return;
        }
        String expanded = resolver == null ? null : resolver.apply(fragment);
        if (expanded == null || expanded.isBlank()) {
            getToolkit().beep();
            return;
        }
        try {
            int caret = getCaretPosition();
            int start = caret - fragment.length();
            suspendUpdates = true;
            try {
                getDocument().remove(start, fragment.length());
                getDocument().insertString(start, expanded, null);
            } finally {
                suspendUpdates = false;
            }
            setCaretPosition(start + expanded.length());
        } catch (BadLocationException e) {
            getToolkit().beep();
        }
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
        sizePopupToContent();
        popup.setVisible(true);
    }

    private record CompletionState(int caretOffset, List<Suggestion> suggestions) {
    }

    private CompletionState gather() {
        if (completionStart < 0) {
            return new CompletionState(-1, List.of());
        }
        try {
            int caret = getCaretPosition();
            String text = getText();
            int lineStart = lineStartOf(text, caret);
            String prefix = text.substring(lineStart, caret);
            // the word behind the trigger
            String word = prefix.substring(completionStart - lineStart + 1);
            var suggestions = suggestionsFor(activeTrigger, word);
            return new CompletionState(caret, suggestions);
        } catch (RuntimeException e) {
            return new CompletionState(-1, List.of());
        }
    }

    /** The offset of the first character of the line containing {@code offset}. */
    private static int lineStartOf(String text, int offset) {
        return text.lastIndexOf('\n', offset - 1) + 1;
    }

    /**
     * Finds the trigger character that starts a completion at (or directly before) the caret, and
     * remembers its offset. A trigger only counts if the text between it and the caret is a
     * plausible word for the given trigger (letters, digits, '_', '.', ':' and, for paths, '/').
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
        return Character.isLetterOrDigit(c) || c == '_' || c == '-' || c == '.' || c == ':'
                || c == '/';
    }

    // --------------------------------------------------------------------------- popup

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

    /**
     * Sizes the popup so that the entries fit without wrapping: the width follows the widest
     * entry, but never falls below the width of the input box (or the last user-chosen width);
     * the height follows the entries up to {@link #MAX_AUTO_POPUP_HEIGHT}. Both are capped at the
     * screen bounds.
     */
    private void sizePopupToContent() {
        var content = list.getPreferredSize();
        var grip = resizeGrip.getPreferredSize();
        int width = Math.max(content.width + POPUP_MARGIN, Math.max(getWidth(), userPopupWidth));
        int height = Math.max(userPopupHeight,
            Math.min(content.height, MAX_AUTO_POPUP_HEIGHT) + grip.height + 4);
        Rectangle screen = getGraphicsConfiguration() != null
                ? getGraphicsConfiguration().getBounds()
                : new Rectangle(Toolkit.getDefaultToolkit().getScreenSize());
        Point loc = popup.getLocation();
        width = Math.min(width, screen.x + screen.width - loc.x - 8);
        height = Math.min(height, screen.y + screen.height - loc.y - 8);
        popup.setSize(Math.max(MIN_POPUP_WIDTH, width), Math.max(MIN_POPUP_HEIGHT, height));
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
        popup.setVisible(false);
        if (sel.action() != null) {
            sel.action().run();
            return;
        }
        if (sel.insert() == null) {
            return;
        }
        try {
            // capture the range before modifying: the document listeners recompute the
            // completion state (and clear completionStart) on every change
            int start = completionStart;
            int end = getCaretPosition();
            if (start < 0 || end < start) {
                return;
            }
            suspendUpdates = true;
            try {
                getDocument().remove(start, end - start);
                getDocument().insertString(start, sel.insert(), null);
                setCaretPosition(start + sel.insert().length());
            } finally {
                suspendUpdates = false;
            }
        } catch (BadLocationException e) {
            getToolkit().beep();
        }
    }

    /**
     * Small drag handle in the bottom-right corner of the completion popup. Dragging it (SE cursor)
     * resizes the popup; the chosen size is kept while the popup is re-shown during typing.
     */
    private final class ResizeGrip extends JComponent {
        private @Nullable Point pressPoint;
        private @Nullable Dimension sizeAtPress;

        ResizeGrip() {
            setPreferredSize(new Dimension(16, 12));
            setCursor(Cursor.getPredefinedCursor(Cursor.SE_RESIZE_CURSOR));
            addMouseListener(new MouseAdapter() {
                @Override
                public void mousePressed(MouseEvent e) {
                    pressPoint = e.getLocationOnScreen();
                    sizeAtPress = popup.getSize();
                }

                @Override
                public void mouseReleased(MouseEvent e) {
                    pressPoint = null;
                }
            });
            addMouseMotionListener(new MouseMotionAdapter() {
                @Override
                public void mouseDragged(MouseEvent e) {
                    if (pressPoint == null || sizeAtPress == null) {
                        return;
                    }
                    int dx = e.getLocationOnScreen().x - pressPoint.x;
                    int dy = e.getLocationOnScreen().y - pressPoint.y;
                    userPopupWidth = Math.max(MIN_POPUP_WIDTH, sizeAtPress.width + dx);
                    userPopupHeight = Math.max(MIN_POPUP_HEIGHT, sizeAtPress.height + dy);
                    popup.setSize(userPopupWidth, userPopupHeight);
                }
            });
        }

        @Override
        protected void paintComponent(Graphics g) {
            super.paintComponent(g);
            var g2 = (Graphics2D) g.create();
            g2.setColor(Color.GRAY);
            for (int i = 0; i < 3; i++) {
                int x1 = getWidth() - 6 - i * 4 - 2;
                int y1 = getHeight() - 2;
                int x2 = getWidth() - 2;
                int y2 = getHeight() - 6 - i * 4 - 2;
                g2.drawLine(x1, y1, x2, y2);
            }
            g2.dispose();
        }
    }
}
