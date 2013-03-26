/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.Font;

/**
 *
 * @author Kai Wallisch
 */
public class EmptySequent extends SequentView {

    public EmptySequent() {
        titleButton.setFontStyle(Font.ITALIC);
        titleButton.setCursor(getCursor());
        titleButton.setForeground(Color.GRAY);
        titleButton.removeMouseListener(titleButton);
    }

    public String getTitle() {
        return "No proof loaded";
    }
}
