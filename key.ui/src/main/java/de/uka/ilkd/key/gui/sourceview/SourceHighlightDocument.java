/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.sourceview;


import java.awt.*;
import java.util.List;
import java.util.Timer;
import java.util.TimerTask;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;
import javax.swing.text.*;


/**
 * This document knows about syntax highlighting.
 *
 * It uses a lexer to determine the syntax highlighting for the text that it contains.
 *
 * There is a timer that triggers the re-parsing of the text after a certain time of inactivity.
 * Currently the entire text is reparsed when needed. This is less efficient than in other
 * frameworks
 * that work line-based, but probably good enough for our purposes.
 *
 * @author Mattias Ulbrich
 */
public class SourceHighlightDocument extends DefaultStyledDocument {

    /**
     * How long to wait after the last change before re-parsing the text.
     */
    private static final long SYNTAX_HIGHLIGHTING_REFRESH_INTERVAL = 800;

    /**
     * The timer that triggers the re-parsing of the text.
     */
    private Timer refreshTimer = new Timer();

    /**
     * The listener that triggers the re-parsing of the text.
     */
    private final DocumentListener docListener = new DocumentListener() {
        @Override
        public void insertUpdate(DocumentEvent documentEvent) {
            restartTimer();
        }

        @Override
        public void removeUpdate(DocumentEvent documentEvent) {
            restartTimer();
        }

        @Override
        public void changedUpdate(DocumentEvent documentEvent) {
            // this seems to enter an infinite loop
            // restartTimer();
        }
    };

    /**
     * Tokens are the entities returned by the lexer. They contain the length of the token and the
     * attributes that should be applied to it.
     *
     * @param len positive length of the token
     * @param attributes to be applied to the span of text
     */
    public record Token(int len, AttributeSet attributes) {
    }

    /**
     * An editor lexer is a function that takes a string and returns a list of tokens that describe
     * the syntax highlighting of the string.
     */
    public interface EditorLexer {
        /**
         * Parse the given non-null text into a list of tokens
         *
         * @param text non-null text to parse
         * @return non-null list of tokens
         */
        List<Token> applyTo(String text);
    }

    /**
     * A trivial lexer that does no syntax highlighting at all.
     */
    public static final EditorLexer TRIVIAL_LEXER = new EditorLexer() {
        @Override
        public List<Token> applyTo(String text) {
            return List.of(new Token(text.length(), new SimpleAttributeSet()));
        }
    };

    /**
     * The lexer that this document uses to determine the syntax highlighting.
     */
    private final EditorLexer lexer;

    /**
     * Create a new document that uses the given lexer for syntax highlighting.
     *
     * @param lexer the lexer to use
     */
    public SourceHighlightDocument(EditorLexer lexer) {
        this.lexer = lexer;
        // workaround for #1641: typing "enter" key shall insert only "\n", even on Windows
        putProperty(DefaultEditorKit.EndOfLineStringProperty, "\n");
        addDocumentListener(docListener);
    }

    private void restartTimer() {
        refreshTimer.cancel();
        refreshTimer = new Timer();
        final TimerTask task = new TimerTask() {
            @Override
            public void run() {
                reparse();
            }
        };
        refreshTimer.schedule(task, SYNTAX_HIGHLIGHTING_REFRESH_INTERVAL);
    }

    private void reparse() {
        try {
            String text = getText(0, getLength());
            List<Token> tokens = lexer.applyTo(text);
            int pos = 0;
            for (Token token : tokens) {
                setCharacterAttributes(pos, token.len(), token.attributes(), true);
                pos += token.len();
            }
        } catch (BadLocationException e) {
            e.printStackTrace();
            throw new RuntimeException(e);
        }
    }

}
