/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import javax.swing.text.BadLocationException;
import javax.swing.text.Highlighter;
import javax.swing.text.JTextComponent;

/**
 * Swing highlighter that highlights the current line in a JTextComponent.
 *
 * It delegates all other methods to the standard Highlighter such that it can be used as a drop-in
 * replacement.
 *
 * @author Mattias Ulbrich
 */
public class CurrentLineHighlighter implements Highlighter {
    private static final Color DEFAULT_COLOR = new Color(0, 0, 0, 15);

    private final Highlighter delegate;
    private final Color color;

    private JTextComponent component;

    public CurrentLineHighlighter(Highlighter delegate) {
        this(delegate, DEFAULT_COLOR);
    }

    public CurrentLineHighlighter(Highlighter delegate, Color color) {
        this.delegate = delegate;
        this.color = color;
    }

    @Override
    public void install(JTextComponent jTextComponent) {
        delegate.install(jTextComponent);
        this.component = jTextComponent;
        component.addCaretListener(e -> component.repaint());
    }

    @Override
    public void deinstall(JTextComponent jTextComponent) {
        delegate.deinstall(jTextComponent);
    }

    @Override
    public void paint(Graphics graphics) {
        delegate.paint(graphics);
        if (component != null) {
            int caretPosition = component.getCaretPosition();
            int currentRow =
                component.getDocument().getDefaultRootElement().getElementIndex(caretPosition);
            try {
                Rectangle modelToView = component.modelToView(component.getDocument()
                        .getDefaultRootElement().getElement(currentRow).getStartOffset());
                graphics.setColor(color);
                graphics.fillRect(0, modelToView.y, component.getWidth(), modelToView.height);
            } catch (BadLocationException e) {
                e.printStackTrace();
            }
        }
    }

    @Override
    public Object addHighlight(int i, int i1, HighlightPainter highlightPainter)
            throws BadLocationException {
        return delegate.addHighlight(i, i1, highlightPainter);
    }

    @Override
    public void removeHighlight(Object o) {
        delegate.removeHighlight(o);
    }

    @Override
    public void removeAllHighlights() {
        delegate.removeAllHighlights();
    }

    @Override
    public void changeHighlight(Object o, int i, int i1) throws BadLocationException {
        delegate.changeHighlight(o, i, i1);
    }

    @Override
    public Highlight[] getHighlights() {
        return delegate.getHighlights();
    }
}
