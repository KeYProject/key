// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.fonticons;

import java.awt.Color;
import java.awt.Image;
import java.net.URL;
import java.util.HashMap;

import javax.swing.Icon;
import javax.swing.ImageIcon;

import de.uka.ilkd.key.util.Debug;

public final class IconFactory {
    public static final IconFontProvider QUIT =
            new IconFontProvider(FontAwesomeSolid.WINDOW_CLOSE);
    public static final IconFontProvider RECENT_FILES =
            new IconFontProvider(FontAwesomeSolid.CLOCK);
    public static final IconFontProvider SEARCH =
            new IconFontProvider(FontAwesomeSolid.SEARCH);
    public static final IconFontProvider SEARCH2 =
            new IconFontProvider(FontAwesomeSolid.SEARCH_LOCATION);
    public static final IconFontProvider STATISTICS =
            new IconFontProvider(FontAwesomeSolid.THERMOMETER_HALF);
    public static final IconFontProvider TOOLBOX =
            new IconFontProvider(FontAwesomeSolid.TOOLBOX);
    public static final IconFontProvider PLUS =
            new IconFontProvider(FontAwesomeSolid.PLUS_CIRCLE);
    public static final IconFontProvider MINUS =
            new IconFontProvider(FontAwesomeSolid.MINUS_CIRCLE);
    public static final IconFontProvider NEXT =
            new IconFontProvider(FontAwesomeSolid.ARROW_RIGHT);
    public static final IconFontProvider PREVIOUS =
            new IconFontProvider(FontAwesomeSolid.ARROW_LEFT);
    public static final IconFontProvider START =
            new IconFontProvider(FontAwesomeSolid.PLAY, Color.GREEN);
    public static final IconFontProvider STOP =
            new IconFontProvider(FontAwesomeSolid.STOP, Color.RED);
    public static final IconFontProvider CLOSE =
            new IconFontProvider(FontAwesomeSolid.TIMES); // OR TIMES_CIRCLE
    public static final IconFontProvider CONFIGURE_MENU =
            new IconFontProvider(FontAwesomeSolid.SORT_DOWN);
    public static final IconFontProvider OPEN_MOST_RECENT =
            new IconFontProvider(FontAwesomeSolid.REDO_ALT);
    public static final IconFontProvider OPEN_EXAMPLES =
            new IconFontProvider(FontAwesomeSolid.IMAGES);
    public static final IconFontProvider OPEN_KEY_FILE =
            new IconFontProvider(FontAwesomeSolid.FOLDER_OPEN);
    public static final IconFontProvider SAVE_FILE =
            new IconFontProvider(FontAwesomeSolid.SAVE);
    public static final IconFontProvider SAVE_BUNDLE =
            new IconFontProvider(FontAwesomeRegular.SAVE);
    public static final IconFontProvider EDIT =
            new IconFontProvider(FontAwesomeSolid.EDIT);
    public static final IconFontProvider INTERACTIVE =
            new IconFontProvider(FontAwesomeSolid.HAND_POINT_RIGHT);
    public static final IconFontProvider PRUNE =
            new IconFontProvider(FontAwesomeSolid.CUT);
    public static final IconFontProvider GOAL_BACK =
            new IconFontProvider(FontAwesomeSolid.BACKSPACE);
    public static final IconFontProvider EXPAND_GOALS =
            new IconFontProvider(FontAwesomeSolid.EXPAND_ARROWS_ALT);
    public static final IconFontProvider CONFIGURE =
            new IconFontProvider(FontAwesomeSolid.COG);
    public static final IconFontProvider HELP =
            new IconFontProvider(FontAwesomeSolid.QUESTION_CIRCLE);
    public static final IconFontProvider PROOF_MANAGEMENT =
            new IconFontProvider(FontAwesomeSolid.TASKS);
    public static final IconFontProvider PROPERTIES =
            new IconFontProvider(FontAwesomeSolid.COG);
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
    public static final IconFontProvider ORIGIN_ICON =
            new IconFontProvider(FontAwesomeSolid.ROUTE);
    public static final IconFontProvider WINDOW_ICON =
            new IconFontProvider(FontAwesomeSolid.WINDOW_RESTORE);

    /**
     * PLUS SQUARED
     */
    public static final IconProvider PLUS_SQUARED
            = new IconFontProvider(FontAwesomeSolid.PLUS_SQUARE);

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
    public static final IconProvider PROOF_TREE =
            new IconFontProvider(FontAwesomeSolid.SITEMAP); //OR CODE_BRANCH
    public static final IconProvider INFO_VIEW =
            new IconFontProvider(FontAwesomeSolid.INFO_CIRCLE);
    public static final IconProvider TREE_NODE_EXPANDED =
            new IconFontProvider(FontAwesomeSolid.CARET_DOWN);
    public static final IconProvider TREE_NODE_RETRACTED =
            new IconFontProvider(FontAwesomeSolid.CARET_RIGHT);
    public static final IconProvider WARNING_UNSOUND =
            new IconFontProvider(FontAwesomeSolid.EXCLAMATION_TRIANGLE, ERROR_COLOR);
    public static final IconProvider WARNING_INCOMPLETE =
            new IconFontProvider(FontAwesomeSolid.EXCLAMATION_TRIANGLE, WARNING_COLOR);
    public static final IconProvider SEARCH_REGROUP =
            new IconFontProvider(FontAwesomeSolid.VIDEO);
    public static final IconProvider EXPORT_MU_SCRIPT =
            new IconFontProvider(FontAwesomeSolid.FILE_EXPORT);
    public static final IconProvider EXPORT_MU_SCRIPT_CLIPBOARD =
            new IconFontProvider(FontAwesomeRegular.COPY);
    public static final IconProvider INTERLOG_LOAD =
            new IconFontProvider(FontAwesomeSolid.TRUCK_LOADING);
    public static final IconProvider INTERLOG_SAVE =
            new IconFontProvider(FontAwesomeRegular.SAVE);
    public static final IconProvider INTERLOG_ADD_USER_NOTE =
            new IconFontProvider(FontAwesomeRegular.STICKY_NOTE);
    public static final IconProvider INTERLOG_TOGGLE_FAV =
            new IconFontProvider(FontAwesomeSolid.HEART);
    public static final IconProvider JUMP_INTO_TREE =
            new IconFontProvider(FontAwesomeSolid.MAP_MARKED);
    public static final IconProvider INTERLOG_TRY_APPLY =
            new IconFontProvider(FontAwesomeSolid.REDO);
    public static final IconProvider INTERLOG_EXPORT_KPS =
            new IconFontProvider(FontAwesomeSolid.FILE_EXPORT);
    public static final IconProvider INTERLOG_EXPORT_MARKDOWN =
            new IconFontProvider(FontAwesomeSolid.FILE_EXPORT);
    public static final IconProvider INTERLOW_EXTENDED_ACTIONS =
            new IconFontProvider(FontAwesomeSolid.WRENCH);
    public static final IconProvider INTERLOG_RESUME =
            new IconFontProvider(FontAwesomeSolid.PAUSE_CIRCLE);
    public static final IconProvider INTERLOG_PAUSE =
            new IconFontProvider(FontAwesomeSolid.PLAY_CIRCLE);
    public static final IconProvider INTERLOG_ICON =
            new IconFontProvider(FontAwesomeSolid.BOOK);

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
    public static final IconFontProvider ABONDON =
            new IconFontProvider(FontAwesomeSolid.TRASH_ALT);
    public static final IconFontProvider SEARCH_HIDE =
            new IconFontProvider(FontAwesomeSolid.LOW_VISION);
    public static final IconFontProvider SEARCH_NEXT =
            new IconFontProvider(FontAwesomeSolid.ARROW_LEFT);
    public static final IconFontProvider ORIGIN_LABELS =
            new IconFontProvider(FontAwesomeSolid.ROUTE);

    private static Image keyHole = getImage("images/ekey-mono.gif");
    private static Image keyHoleAlmostClosed = getImage("images/ekey-brackets.gif");
    private static Image keyHoleInteractive = getImage("images/keyinteractive.gif");
    private static Image keyHoleLinked = getImage("images/keylinked.gif");
    private static Image keyLogo = getImage("images/key-color.gif");
    private static Image keyLogo22 = getImage("images/key22.gif");
    private static Image keyLogoSmall = getImage("images/key-color-icon-square.png");
    private static Image oneStepSimplifier = getImage("images/toolbar/oneStepSimplifier.png");

    private static Image junit = getImage("images/toolbar/junit_logo.png");
    private static Image jml = getImage("images/toolbar/jml.png");
    private static Image uml = getImage("images/toolbar/uml.png");

    // private static Image expandGoals = getImage("images/toolbar/expandGoals.png");
    // private static Image scriptAppLogo = getImage("images/scriptAppLogo.png");
    // private static Image counterexampleImage = getImage("images/toolbar/ce.png");
    // private static Image testgenerationImage = getImage("images/toolbar/tg.png");
    // private static Image heatmapImage = getImage("images/toolbar/heatmap.png");

    private static HashMap<String, Icon> cache = new HashMap<String, Icon>();

    private IconFactory() {
    }

    public static Image getImage(String s) {
        ImageIcon ii = createImageIcon(IconFactory.class, s);
        return ii != null ? ii.getImage() : null;
    }

    /**
     * Creates an icon from an image contained in a resource.
     * The resource is fist search using the package name of the given class
     * and if the resource is not found the package name of its superclass is used
     * recursively.
     *
     * @param cl       the Class the resource is looked for
     * @param filename String the name of the file to search  (only relative
     *                 pathname to the path of the calling class)
     * @return the newly created image
     */
    private static ImageIcon createImageIcon(Class<?> cl, String filename) {
        filename = "/de/uka/ilkd/key/gui/" + filename;
        URL iconURL = cl.getResource(filename);
        Debug.out("Load Resource:" + filename + " of class " + cl);
        if (iconURL == null && cl.getSuperclass() != null) {
            return createImageIcon(cl.getSuperclass(),
                    filename);
        } else if (iconURL == null && cl.getSuperclass() == null) {
            // error message Resource not found
            System.out.println("No image resource " + filename + " found");
            return null;
        } else {
            Debug.out("Done.");
            return new ImageIcon(iconURL);
        }
    }

    private static ImageIcon scaleIcon(Image im, int x, int y) {
        Image scaledim = im.getScaledInstance(x, y, Image.SCALE_SMOOTH);
        return new ImageIcon(scaledim);
    }

    public static Icon abandon(int x) {
        return ABONDON.load(x);
    }

    public static Icon configure(int x) {
        return CONFIGURE.load(x);
    }

    public static Icon help(int x) {
        //return scaleIcon(help ,x,x);
        return HELP.load(x);
    }

    public static Icon proofMgt(int x) {
        //return scaleIcon(proofMgt ,x,x);
        return PROOF_MANAGEMENT.load(x);
    }

    public static Icon properties(int x) {
        //return IconFontSwing.buildIcon(FontAwesomeSolid.).load(x);
        //return scaleIcon(properties ,x,x);
        return PROPERTIES.load(x);
    }

    public static Icon quit(int x) {
        return QUIT.load(x);
    }

    public static Icon recentFiles(int x) {
        return RECENT_FILES.load(x);
        //return scaleIcon(recentFiles ,x,x);
    }

    public static Icon search(int x) {
        return SEARCH.load(x);
        //return scaleIcon(search ,x,x);
    }

    public static Icon search2(int x) {
        return SEARCH2.load(x);
        //return scaleIcon(search2 ,x,x);
    }

    public static Icon statistics(int x) {
        return STATISTICS.load(x);
        //return scaleIcon(statistics,x,x);
    }

    public static Icon toolbox(int x) {
        return TOOLBOX.load(x);
        //return scaleIcon(toolbox,x,x);
    }

    public static Icon plus(int x) {
        return PLUS.load(x);
        //return scaleIcon(plus,x,x);
    }

    public static Icon minus(int x) {
        return MINUS.load(x);
        //return scaleIcon(minus,x,x);
    }

    public static Icon expandGoals(int x) {
        return EXPAND_GOALS.load(x);
    }

    public static Icon next(int x) {
        return NEXT.load(x);
        //return scaleIcon(next,x,x);
    }

    public static Icon previous(int x) {
        return PREVIOUS.load(x);
        //return scaleIcon(previous,x,x);
    }

    public static Icon stop(int x) {
        return STOP.load(x);
        //return scaleIcon(stop,x,x);
    }

    public static Icon close(int x) {
        return CLOSE.load(x);
        //return scaleIcon(cross,x,x);
    }

    public static ImageIcon keyHole(int x, int y) {
        return scaleIcon(keyHole, x, y);
    }

    public static Icon keyHoleClosed(int x) {
        return GOAL_CLOSED.load(x);
        //return scaleIcon(GOAL_CLOSED, x, y);
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

    public static ImageIcon keyHoleInteractive(int x, int y) {
        return scaleIcon(keyHoleInteractive, x, y);
    }

    public static ImageIcon keyHoleLinked(int x, int y) {
        return scaleIcon(keyHoleLinked, x, y);
    }

    public static ImageIcon keyLogo(int x, int y) {
        return scaleIcon(keyLogo, x, y);
    }

    public static ImageIcon key22Logo(int x, int y) {
        return scaleIcon(keyLogo22, x, y);
    }

    public static Icon autoModeStartLogo(int size) {
        //return scaleIcon(autoModeStart, size, size);
        return AUTO_MODE_START.load(size);
    }

    public static Icon strategyStartLogo(int size) {
        return START.load(size);
    }

    public static Icon autoModeStopLogo(int size) {
        //return scaleIcon(autoModeStop, size, size);
        return AUTO_MODE_STOP.load(size);
    }

    public static Icon selectDecProcArrow(int size) {
        //return scaleIcon(decisionProcedureConfigArrow, size / 2, size);
        return CONFIGURE_MENU.load(size);
    }

    public static Icon oneStepSimplifier(int size) {
        return scaleIcon(oneStepSimplifier, size, size);
    }

    public static Icon testGeneration(int size) {
        return TEST_CASE_GENERATION.get(size);//scaleIcon(testgenerationImage, size, size);
    }

    public static Icon counterExample(int size) {
        return COUNTER_EXAMPLE.get(size);//scaleIcon(counterexampleImage, size, size);
    }

    public static Icon junitLogo(int size) {
        return scaleIcon(junit, size, size);
    }

    public static Icon jmlLogo(int size) {
        return scaleIcon(jml, size, size);
    }

    /*public static Icon umlLogo(int size) {
        return scaleIcon(uml, size, size);
    }*/

    public static Icon pruneLogo(int size) {
        //return scaleIcon(prune, size, size);
        return PRUNE.load(size);
    }

    public static Icon goalBackLogo(int size) {
        //return scaleIcon(goalBack, size, size);
        //alternative UNDO
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
        //return scaleIcon(openMostRecentKeYFile, size, size);
    }

    public static Icon openExamples(int size) {
        return OPEN_EXAMPLES.load(size);
        //return scaleIcon(openExamples, size, size);
    }

    public static Icon openKeYFile(int size) {
        return OPEN_KEY_FILE.load(size);
        //return scaleIcon(openKeYFile, size, size);
    }

    public static Icon saveFile(int size) {
        return SAVE_FILE.load(size);
        //return scaleIcon(saveFile, size, size);
    }

    public static Icon saveBundle(int size) {
        return SAVE_BUNDLE.load(size);
        //return scaleIcon(saveBundle, size, size);
    }

    public static Icon editFile(int size) {
        return EDIT.load(size);
        //return scaleIcon(editFile, size, size);
    }

    public static Icon interactiveAppLogo(int size) {
        return INTERACTIVE.load(size);
        //return scaleIcon(interactiveAppLogo, size, size);
    }

    public static Icon get(IconProvider provider, float size) {
        return cache.computeIfAbsent(provider.getKey(size), d -> provider.load(size));
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