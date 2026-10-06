/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.fonticons;

import javafx.scene.Node;
import javafx.scene.text.Font;
import javafx.scene.text.Text;

/**
 * Factory for the icons of the JavaFX UI, the counter-part of
 * {@code de.uka.ilkd.key.gui.fonticons.IconFactory} in the Swing module {@code key.ui}.
 * <p>
 * Icons are rendered as pure JavaFX {@link Text} nodes using the icon fonts bundled with the
 * module. The text color is controlled by the {@code key-icon} style class, which is themed via
 * {@code key-light.css}/{\code key-dark.css} — no AWT/ImageIcon involved.
 * <p>
 * Only a subset of the semantic keys of the Swing {@code IconFactory} is defined yet; the
 * remaining keys are ported together with the actions that use them (milestone M3).
 */
public final class IconFactoryF {

    /** The default size of icons created via the convenience factory methods. */
    public static final double DEFAULT_SIZE = 14.0;

    /**
     * Style class of icon text nodes; the fill is defined by the theme stylesheets
     * ({@code .key-icon { -fx-fill: -key-text; }}).
     */
    public static final String ICON_STYLE_CLASS = "key-icon";

    /**
     * The semantic icon keys of the JavaFX UI. The glyph assignments mirror the constants of the
     * Swing {@code IconFactory}.
     */
    public enum Key {
        QUIT(FontAwesomeSolid.WINDOW_CLOSE),
        RECENT_FILES(FontAwesomeSolid.CLOCK),
        SEARCH(FontAwesomeSolid.SEARCH),
        STATISTICS(FontAwesomeSolid.THERMOMETER_HALF),
        TOOLBOX(FontAwesomeSolid.TOOLBOX),
        PLUS(FontAwesomeSolid.PLUS_CIRCLE),
        MINUS(FontAwesomeSolid.MINUS_CIRCLE),
        NEXT(FontAwesomeSolid.ARROW_RIGHT),
        PREVIOUS(FontAwesomeSolid.ARROW_LEFT),
        START(FontAwesomeSolid.PLAY),
        STOP(FontAwesomeSolid.STOP),
        CLOSE(FontAwesomeSolid.TIMES),
        OPEN_MOST_RECENT(FontAwesomeSolid.REDO_ALT),
        OPEN_KEY_FILE(FontAwesomeSolid.FOLDER_OPEN),
        SAVE_FILE(FontAwesomeSolid.SAVE),
        EDIT(FontAwesomeSolid.EDIT),
        PRUNE(FontAwesomeSolid.CUT),
        GOAL_BACK(FontAwesomeSolid.BACKSPACE),
        EXPAND_GOALS(FontAwesomeSolid.EXPAND_ARROWS_ALT),
        CONFIGURE(FontAwesomeSolid.COG),
        HELP(FontAwesomeSolid.QUESTION_CIRCLE),
        PROOF_MANAGEMENT(FontAwesomeSolid.TASKS),
        AUTO_MODE_START(FontAwesomeSolid.PLAY_CIRCLE),
        AUTO_MODE_STOP(FontAwesomeSolid.STOP_CIRCLE),
        PROOF_TREE(FontAwesomeSolid.SITEMAP),
        INFO_VIEW(FontAwesomeSolid.INFO_CIRCLE),
        PROOF_SEARCH_STRATEGY(FontAwesomeSolid.COG);

        private final IconFont glyph;

        Key(IconFont glyph) {
            this.glyph = glyph;
        }

        /**
         * @return the glyph backing this key
         */
        public IconFont glyph() {
            return glyph;
        }
    }

    private IconFactoryF() {
    }

    /**
     * Creates an icon for the given semantic key at {@link #DEFAULT_SIZE}.
     *
     * @param key the semantic key
     * @return a new icon node (may be used as a graphic of buttons, menu items and tabs)
     */
    public static Node createIcon(Key key) {
        return createIcon(key, DEFAULT_SIZE);
    }

    /**
     * Creates an icon for the given semantic key at the given size.
     *
     * @param key the semantic key
     * @param size the font size of the icon
     * @return a new icon node
     */
    public static Node createIcon(Key key, double size) {
        return createIcon(key.glyph(), size);
    }

    /**
     * Creates an icon rendering the given glyph at {@link #DEFAULT_SIZE}.
     *
     * @param glyph the glyph
     * @return a new icon node
     */
    public static Node createIcon(IconFont glyph) {
        return createIcon(glyph, DEFAULT_SIZE);
    }

    /**
     * Creates an icon rendering the given glyph at the given size.
     *
     * @param glyph the glyph
     * @param size the font size of the icon
     * @return a new icon node
     */
    public static Node createIcon(IconFont glyph, double size) {
        Text text = new Text(String.valueOf(glyph.getUnicode()));
        text.getStyleClass().add(ICON_STYLE_CLASS);
        javafx.scene.text.Font base = glyph.getFont();
        text.setFont(Font.font(base.getFamily(), size));
        return text;
    }
}
