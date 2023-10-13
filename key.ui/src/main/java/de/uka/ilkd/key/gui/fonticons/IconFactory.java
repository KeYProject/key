/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.fonticons;

import java.awt.*;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import javax.swing.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public final class IconFactory {
    public static final IconFontProvider QUIT = new IconFontProvider(FontAwesomeSolid.WINDOW_CLOSE);
    public static final IconFontProvider RECENT_FILES =
        new IconFontProvider(FontAwesomeSolid.CLOCK);
    public static final IconFontProvider SEARCH = new IconFontProvider(FontAwesomeSolid.SEARCH);
    public static final IconFontProvider SEARCH2 =
        new IconFontProvider(FontAwesomeSolid.SEARCH_LOCATION);
    public static final IconFontProvider STATISTICS =
        new IconFontProvider(FontAwesomeSolid.THERMOMETER_HALF);
    public static final IconFontProvider TOOLBOX = new IconFontProvider(FontAwesomeSolid.TOOLBOX);
    public static final IconFontProvider PLUS = new IconFontProvider(FontAwesomeSolid.PLUS_CIRCLE);
    public static final IconFontProvider MINUS =
        new IconFontProvider(FontAwesomeSolid.MINUS_CIRCLE);
    public static final IconFontProvider NEXT = new IconFontProvider(FontAwesomeSolid.ARROW_RIGHT);
    public static final IconFontProvider PREVIOUS =
        new IconFontProvider(FontAwesomeSolid.ARROW_LEFT);
    public static final IconFontProvider START =
        new IconFontProvider(FontAwesomeSolid.PLAY, Color.GREEN);
    public static final IconFontProvider STOP =
        new IconFontProvider(FontAwesomeSolid.STOP, Color.RED);
    // an alternative would be TIMES_CIRCLE
    public static final IconFontProvider CLOSE = new IconFontProvider(FontAwesomeSolid.TIMES);
    public static final IconFontProvider CONFIGURE_MENU =
        new IconFontProvider(FontAwesomeSolid.SORT_DOWN);
    public static final IconFontProvider OPEN_MOST_RECENT =
        new IconFontProvider(FontAwesomeSolid.REDO_ALT);
    public static final IconFontProvider OPEN_EXAMPLES =
        new IconFontProvider(FontAwesomeSolid.IMAGES);
    public static final IconFontProvider OPEN_KEY_FILE =
        new IconFontProvider(FontAwesomeSolid.FOLDER_OPEN);
    public static final IconFontProvider SAVE_FILE = new IconFontProvider(FontAwesomeSolid.SAVE);
    public static final IconFontProvider SAVE_BUNDLE =
        new IconFontProvider(FontAwesomeRegular.SAVE);
    public static final IconFontProvider EDIT = new IconFontProvider(FontAwesomeSolid.EDIT);
    public static final IconFontProvider INTERACTIVE =
        new IconFontProvider(FontAwesomeSolid.HAND_POINT_RIGHT);
    public static final IconFontProvider SCRIPT = new IconFontProvider(FontAwesomeSolid.SCROLL);
    public static final IconFontProvider BACKREFERENCE =
        new IconFontProvider(FontAwesomeSolid.BACKWARD);
    public static final IconFontProvider BACKREFERENCE_ARROW =
        new IconFontProvider(FontAwesomeSolid.ARROWS_TO_EYE);
    public static final IconFontProvider PRUNE = new IconFontProvider(FontAwesomeSolid.CUT);
    public static final IconFontProvider GOAL_BACK =
        new IconFontProvider(FontAwesomeSolid.BACKSPACE);
    public static final IconFontProvider EXPAND_GOALS =
        new IconFontProvider(FontAwesomeSolid.EXPAND_ARROWS_ALT);
    public static final IconFontProvider CONFIGURE = new IconFontProvider(FontAwesomeSolid.COG);
    public static final IconFontProvider HELP =
        new IconFontProvider(FontAwesomeSolid.QUESTION_CIRCLE);
    public static final IconFontProvider PROOF_MANAGEMENT =
        new IconFontProvider(FontAwesomeSolid.TASKS);
    public static final IconFontProvider PROPERTIES = new IconFontProvider(FontAwesomeSolid.COG);
    public static final IconProvider SEARCH_PREV =
        new IconFontProvider(FontAwesomeSolid.ARROW_RIGHT);
    public static final IconFontProvider EXPERIMENTAL_EXTENSION =
        new IconFontProvider(FontAwesomeSolid.FLASK);
    public static final IconFontProvider COUNTER_EXAMPLE =
        new IconFontProvider(FontAwesomeSolid.BOMB); // OR BUG or BOLT
    public static final IconFontProvider TEST_CASE_GENERATION =
        new IconFontProvider(FontAwesomeSolid.VIALS); // OR VIAL
    public static final IconFontProvider ORIGIN_HIGHLIGHT_ICON =
        new IconFontProvider(FontAwesomeSolid.HIGHLIGHTER);
    public static final IconFontProvider ORIGIN_ICON = new IconFontProvider(FontAwesomeSolid.ROUTE);
    public static final IconFontProvider WINDOW_ICON =
        new IconFontProvider(FontAwesomeSolid.WINDOW_RESTORE);
    /**
     * Icon for the proof slicing extension.
     * Used in the title of the extension panel.
     */
    public static final IconFontProvider SLICE_ICON =
        new IconFontProvider(FontAwesomeSolid.ALIGN_JUSTIFY);
    /**
     * Icon for proof steps marked as useless.
     * Used in the proof tree panel.
     */
    public static final IconFontProvider USELESS_APP_ICON =
        new IconFontProvider(FontAwesomeSolid.TIMES);

    /**
     * PLUS SQUARED
     */
    public static final IconProvider PLUS_SQUARED =
        new IconFontProvider(FontAwesomeSolid.PLUS_SQUARE);

    public static final float DEFAULT_SIZE = 16;
    public static final Color CLOSED_GREEN = DuneColorScheme.green;
    public static final Color BLUE = DuneColorScheme.blue;
    public static final Color ERROR_COLOR = DuneColorScheme.red;
    public static final Color WARNING_COLOR = DuneColorScheme.orange;
    public static final Color LINKED_FOLDER_COLOR = new Color(255, 0, 240);
    public static final Color CLOSABLE_FOLDER_COLOR = Color.blue.darker();
    public static final IconFontProvider AUTO_MODE_START =
        new IconFontProvider(FontAwesomeSolid.PLAY_CIRCLE, CLOSED_GREEN);
    public static final IconFontProvider AUTO_MODE_STOP =
        new IconFontProvider(FontAwesomeSolid.STOP_CIRCLE, ERROR_COLOR);
    public static final IconProvider PROOF_SEARCH_STRATEGY =
        new IconFontProvider(FontAwesomeSolid.COG);
    // an alternative would be CODE_BRANCH
    public static final IconProvider PROOF_TREE = new IconFontProvider(FontAwesomeSolid.SITEMAP);
    public static final IconProvider INFO_VIEW = new IconFontProvider(FontAwesomeSolid.INFO_CIRCLE);
    public static final IconProvider TREE_NODE_EXPANDED =
        new IconFontProvider(FontAwesomeSolid.CARET_DOWN);
    public static final IconProvider TREE_NODE_RETRACTED =
        new IconFontProvider(FontAwesomeSolid.CARET_RIGHT);
    public static final IconProvider WARNING_UNSOUND =
        new IconFontProvider(FontAwesomeSolid.EXCLAMATION_TRIANGLE, ERROR_COLOR);
    public static final IconProvider WARNING_INCOMPLETE =
        new IconFontProvider(FontAwesomeSolid.EXCLAMATION_TRIANGLE, WARNING_COLOR);
    public static final IconProvider SEARCH_REGROUP = new IconFontProvider(FontAwesomeSolid.VIDEO);
    public static final IconProvider EXPORT_MU_SCRIPT =
        new IconFontProvider(FontAwesomeSolid.FILE_EXPORT);
    public static final IconProvider EXPORT_MU_SCRIPT_CLIPBOARD =
        new IconFontProvider(FontAwesomeRegular.COPY);
    public static final IconProvider JUMP_INTO_TREE =
        new IconFontProvider(FontAwesomeSolid.MAP_MARKED);

    public static final IconProvider HEATMAP_DEACTIVATE =
        new IconFontProvider(FontAwesomeSolid.SHOE_PRINTS);
    public static final IconProvider HEATMAP_ACTIVATE =
        new IconFontProvider(FontAwesomeSolid.SHOE_PRINTS);

    public static final IconFontProvider PROVED_FOLDER_ICON =
        new IconFontProvider(FontAwesomeSolid.FOLDER, CLOSED_GREEN);
    public static final IconFontProvider LINKED_FOLDER_ICON =
        new IconFontProvider(FontAwesomeSolid.FOLDER, LINKED_FOLDER_COLOR);
    public static final IconFontProvider CLOSABLE_FOLDER_ICON =
        new IconFontProvider(FontAwesomeSolid.FOLDER, CLOSABLE_FOLDER_COLOR);
    public static final IconFontProvider GOAL_CLOSED =
        new IconFontProvider(FontAwesomeSolid.CHECK, CLOSED_GREEN);
    public static final IconFontProvider SELECT_GOAL_ABOVE =
        new IconFontProvider(FontAwesomeSolid.ANGLE_UP);
    public static final IconFontProvider SELECT_GOAL_BELOW =
        new IconFontProvider(FontAwesomeSolid.ANGLE_DOWN);
    public static final IconFontProvider SEARCH_HIGHLIGHT =
        new IconFontProvider(FontAwesomeSolid.HIGHLIGHTER);
    public static final IconFontProvider ABANDON = new IconFontProvider(FontAwesomeSolid.TRASH_ALT);
    public static final IconFontProvider SEARCH_HIDE =
        new IconFontProvider(FontAwesomeSolid.LOW_VISION);
    public static final IconFontProvider SEARCH_NEXT =
        new IconFontProvider(FontAwesomeSolid.ARROW_LEFT);
    public static final IconFontProvider ORIGIN_LABELS =
        new IconFontProvider(FontAwesomeSolid.ROUTE);

    private static final Logger LOGGER = LoggerFactory.getLogger(IconFactory.class);

    private static final Image keyHole = getImage("images/ekey-mono.gif");
    private static final Image keyHoleAlmostClosed = getImage("images/ekey-brackets.gif");
    private static final Image keyCachedClosed = getImage("images/closed-cached.png");
    private static final Image keyHoleInteractive = getImage("images/keyinteractive.gif");
    private static final Image keyHoleLinked = getImage("images/keylinked.gif");
    private static final Image keyLogo = getImage("images/key-color.png");
    private static final Image keyLogoShadow = getImage("images/key-shadow.png");
    // The following should be updated with every major version step.
    private static final Image keyVersionLogo = getImage("images/key-shadow-2.12.png");
    private static final Image keyLogoSmall = getImage("images/key-color-icon-square.gif");
    private static final Image oneStepSimplifier = getImage("images/toolbar/oneStepSimplifier.png");

    private static final Image junit = getImage("images/toolbar/junit_logo.png");
    private static final Image jml = getImage("images/toolbar/jml.png");
    private static final Image uml = getImage("images/toolbar/uml.png");

    // private static Image expandGoals = getImage("images/toolbar/expandGoals.png");
    // private static Image scriptAppLogo = getImage("images/scriptAppLogo.png");
    // private static Image counterexampleImage = getImage("images/toolbar/ce.png");
    // private static Image testgenerationImage = getImage("images/toolbar/tg.png");
    // private static Image heatmapImage = getImage("images/toolbar/heatmap.png");

    private static final HashMap<String, Icon> cache = new HashMap<>();

    private IconFactory() {
    }

    public static Image getImage(String s) {
        ImageIcon ii = createImageIcon(s);
        return ii != null ? ii.getImage() : null;
    }

    /**
     * Creates an icon from an image contained in a resource.
     *
     * @param filename String the name of the file to search (only relative pathname to the path of
     *        this class)
     * @return the newly created image
     */
    private static ImageIcon createImageIcon(String filename) {
        filename = "/de/uka/ilkd/key/gui/" + filename;
        URL iconURL = IconFactory.class.getResource(filename);
        if (iconURL == null) {
            // error message Resource not found
            LOGGER.warn("No resource " + filename + " found");
            return null;
        } else {
            LOGGER.trace("Loaded resource: " + filename);
            return new ImageIcon(iconURL);
        }
    }

    private static ImageIcon scaleIcon(Image im, int x, int y) {
        if (im.getWidth(null) == x && im.getHeight(null) == y) {
            return new ImageIcon(im);
        }
        Image scaledim = im.getScaledInstance(x, y, Image.SCALE_SMOOTH);
        return new ImageIcon(scaledim);
    }

    public static Icon abandon(int x) {
        return ABANDON.load(x);
    }

    public static Icon configure(int x) {
        return CONFIGURE.load(x);
    }

    public static Icon help(int x) {
        // return scaleIcon(help ,x,x);
        return HELP.load(x);
    }

    public static Icon proofMgt(int x) {
        // return scaleIcon(proofMgt ,x,x);
        return PROOF_MANAGEMENT.load(x);
    }

    public static Icon properties(int x) {
        // return IconFontSwing.buildIcon(FontAwesomeSolid.).load(x);
        // return scaleIcon(properties ,x,x);
        return PROPERTIES.load(x);
    }

    public static Icon quit(int x) {
        return QUIT.load(x);
    }

    public static Icon recentFiles(int x) {
        return RECENT_FILES.load(x);
        // return scaleIcon(recentFiles ,x,x);
    }

    public static Icon search(int x) {
        return SEARCH.load(x);
        // return scaleIcon(search ,x,x);
    }

    public static Icon search2(int x) {
        return SEARCH2.load(x);
        // return scaleIcon(search2 ,x,x);
    }

    public static Icon statistics(int x) {
        return STATISTICS.load(x);
        // return scaleIcon(statistics,x,x);
    }

    public static Icon toolbox(int x) {
        return TOOLBOX.load(x);
        // return scaleIcon(toolbox,x,x);
    }

    public static Icon plus(int x) {
        return PLUS.load(x);
        // return scaleIcon(plus,x,x);
    }

    public static Icon minus(int x) {
        return MINUS.load(x);
        // return scaleIcon(minus,x,x);
    }

    public static Icon expandGoals(int x) {
        return EXPAND_GOALS.load(x);
    }

    public static Icon next(int x) {
        return NEXT.load(x);
        // return scaleIcon(next,x,x);
    }

    public static Icon previous(int x) {
        return PREVIOUS.load(x);
        // return scaleIcon(previous,x,x);
    }

    public static Icon stop(int x) {
        return STOP.load(x);
        // return scaleIcon(stop,x,x);
    }

    public static Icon close(int x) {
        return CLOSE.load(x);
        // return scaleIcon(cross,x,x);
    }

    public static ImageIcon keyHole(int x, int y) {
        return scaleIcon(keyHole, x, y);
    }

    public static Icon keyHoleClosed(int height) {
        return GOAL_CLOSED.load(height);
        // return scaleIcon(GOAL_CLOSED, x, y);
    }

    public static Icon selectGoalAbove(int size) {
        return SELECT_GOAL_ABOVE.load(size);
    }

    public static Icon selectGoalBelow(int size) {
        return SELECT_GOAL_BELOW.load(size);
    }

    public static ImageIcon keyHoleAlmostClosed(int x, int y) {
        return scaleIcon(keyHoleAlmostClosed, x, y);
    }

    public static ImageIcon keyCachedClosed(int x, int y) {
        return scaleIcon(keyCachedClosed, x, y);
    }

    public static ImageIcon keyHoleInteractive(int x, int y) {
        return scaleIcon(keyHoleInteractive, x, y);
    }

    public static ImageIcon keyHoleLinked(int x, int y) {
        return scaleIcon(keyHoleLinked, x, y);
    }

    public static ImageIcon keyLogo(int x, int y) {
        return scaleIcon(keyLogo, x, y);
    }

    public static Icon keyVersionLogo() {
        return new ImageIcon(keyVersionLogo);
    }

    public static Icon keyVersionLogo(int x, int y) {
        return scaleIcon(keyVersionLogo, x, y);
    }

    public static Icon autoModeStartLogo(int size) {
        // return scaleIcon(autoModeStart, size, size);
        return AUTO_MODE_START.load(size);
    }

    public static Icon strategyStartLogo(int size) {
        return START.load(size);
    }

    public static Icon autoModeStopLogo(int size) {
        // return scaleIcon(autoModeStop, size, size);
        return AUTO_MODE_STOP.load(size);
    }

    public static Icon selectDecProcArrow(int size) {
        // return scaleIcon(decisionProcedureConfigArrow, size / 2, size);
        return CONFIGURE_MENU.load(size);
    }

    public static Icon oneStepSimplifier(int size) {
        return scaleIcon(oneStepSimplifier, size, size);
    }

    public static Icon testGeneration(int size) {
        return TEST_CASE_GENERATION.get(size);// scaleIcon(testgenerationImage, size, size);
    }

    public static Icon counterExample(int size) {
        return COUNTER_EXAMPLE.get(size);// scaleIcon(counterexampleImage, size, size);
    }

    public static Icon junitLogo(int size) {
        return scaleIcon(junit, size, size);
    }

    public static Icon jmlLogo(int size) {
        return scaleIcon(jml, size, size);
    }

    /*
     * public static Icon umlLogo(int size) { return scaleIcon(uml, size, size); }
     */

    public static Icon pruneLogo(int size) {
        // return scaleIcon(prune, size, size);
        return PRUNE.load(size);
    }

    public static Icon goalBackLogo(int size) {
        // return scaleIcon(goalBack, size, size);
        // alternative UNDO
        return GOAL_BACK.load(size);
    }

    public static Icon provedFolderIcon(int height) {
        return PROVED_FOLDER_ICON.load(height);
    }

    public static Icon linkedFolderIcon(int height) {
        return LINKED_FOLDER_ICON.load(height);
    }

    public static Icon closableFolderIcon(int height) {
        return CLOSABLE_FOLDER_ICON.load(height);
    }

    public static Icon expandedIcon(int height) {
        return TREE_NODE_EXPANDED.load(height);
    }

    public static Icon collapsedIcon(int height) {
        return TREE_NODE_RETRACTED.load(height);
    }

    public static Image keyLogo() {
        return keyLogoSmall;
    }

    public static Icon openMostRecent(int size) {
        return OPEN_MOST_RECENT.load(size);
        // return scaleIcon(openMostRecentKeYFile, size, size);
    }

    public static Icon openExamples(int size) {
        return OPEN_EXAMPLES.load(size);
        // return scaleIcon(openExamples, size, size);
    }

    public static Icon openKeYFile(int size) {
        return OPEN_KEY_FILE.load(size);
        // return scaleIcon(openKeYFile, size, size);
    }

    public static Icon saveFile(int size) {
        return SAVE_FILE.load(size);
        // return scaleIcon(saveFile, size, size);
    }

    public static Icon saveBundle(int size) {
        return SAVE_BUNDLE.load(size);
        // return scaleIcon(saveBundle, size, size);
    }

    public static Icon editFile(int size) {
        return EDIT.load(size);
        // return scaleIcon(editFile, size, size);
    }

    /**
     * @param size desired icon size
     * @return the icon to use for useless proof steps
     */
    public static Icon uselessAppLogo(int size) {
        return USELESS_APP_ICON.load(size);
    }

    public static Icon interactiveAppLogo(int size) {
        return INTERACTIVE.load(size);
        // return scaleIcon(interactiveAppLogo, size, size);
    }

    public static Icon scriptAppLogo(int size) {
        return SCRIPT.load(size);
        // return scaleIcon(interactiveAppLogo, size, size);
    }

    public static Icon get(IconProvider provider, float size) {
        return cache.computeIfAbsent(provider.getKey(size), d -> provider.load(size));
    }

    /**
     * Returns a list of the application logo (used in Frame, Taskbar, etc) in various predefined
     * sizes.
     */
    public static List<? extends Image> applicationLogos() {
        // https://stackoverflow.com/questions/18224184/sizes-of-frame-icons-used-in-swing
        Image original = keyLogo();
        int[] sizes = new int[] { 16, 20, 32, 40, 64, 128 };
        ArrayList<Image> images = new ArrayList<>(sizes.length);
        for (int sz : sizes) {
            images.add(original.getScaledInstance(sz, sz, Image.SCALE_SMOOTH));
        }
        return images;
    }
}


/**
 * @see <https://atelierbram.github.io/syntax-highlighting/atelier-schemes/dune/>
 */
class DuneColorScheme {
    public static final Color base00 = hex("#20201d");
    public static final Color base01 = hex("#292824");
    public static final Color base02 = hex("#6e6b5e");
    public static final Color base03 = hex("#7d7a68");
    public static final Color base04 = hex("#999580");
    public static final Color base05 = hex("#a6a28c");
    public static final Color base06 = hex("#e8e4cf");
    public static final Color base07 = hex("#fefbec");
    public static final Color base08 = hex("#d73737");
    public static final Color base09 = hex("#b65611");
    public static final Color base0a = hex("#ae9513");
    public static final Color base0b = hex("#60ac39");
    public static final Color base0c = hex("#1fad83");
    public static final Color base0d = hex("#6684e1");
    public static final Color base0e = hex("#b854d4");
    public static final Color base0f = hex("#d43552");
    public static final Color red = base08;
    public static final Color orange = base09;
    public static final Color yellow = base0a;
    public static final Color green = base0b;
    public static final Color cyan = base0c;
    public static final Color blue = base0d;
    public static final Color violet = base0e;
    public static final Color magenta = base0f;

    private static Color hex(String s) {
        return Color.decode(s);
    }
}
