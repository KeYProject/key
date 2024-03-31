/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

import java.awt.*;
import javax.swing.event.ChangeListener;
import javax.swing.text.Caret;
import javax.swing.text.JTextComponent;

/**
 * A caret that does nothing.
 *
 * This implementation is used disable in SequentViews. The problem is that manually selected text
 * interferes with the automatic highlights for drag-n-drop and mouseover.
 *
 * All methods return default values or do nothing.
 *
 * @author Mattias Ulbrich
 */
public class DoNothingCaret implements Caret {
    public static final Caret INSTANCE = new DoNothingCaret();

    @Override
    public void install(JTextComponent c) {

    }

    @Override
    public void deinstall(JTextComponent c) {

    }

    @Override
    public void paint(Graphics g) {

    }

    @Override
    public void addChangeListener(ChangeListener l) {

    }

    @Override
    public void removeChangeListener(ChangeListener l) {

    }

    @Override
    public boolean isVisible() {
        return false;
    }

    @Override
    public void setVisible(boolean v) {

    }

    @Override
    public boolean isSelectionVisible() {
        return false;
    }

    @Override
    public void setSelectionVisible(boolean v) {

    }

    @Override
    public void setMagicCaretPosition(Point p) {

    }

    @Override
    public Point getMagicCaretPosition() {
        return new Point(0, 0);
    }

    @Override
    public void setBlinkRate(int rate) {

    }

    @Override
    public int getBlinkRate() {
        return 0;
    }

    @Override
    public int getDot() {
        return 0;
    }

    @Override
    public int getMark() {
        return 0;
    }

    @Override
    public void setDot(int dot) {

    }

    @Override
    public void moveDot(int dot) {

    }
}
