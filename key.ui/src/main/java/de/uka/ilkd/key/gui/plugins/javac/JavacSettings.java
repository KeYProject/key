/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.javac;
import java.lang.Boolean;

import de.uka.ilkd.key.settings.AbstractPropertiesSettings;

/**
 * Settings for the javac extention.
 *
 * @author PiisRational
 */
public class JavacSettings extends AbstractPropertiesSettings {

    public static final String CATEGORY = "Type Checking";

    /**
     * Config key for {@link #checkers}.
     */
    private static final String KEY_USE_CHECKERS = "useCheckers";

    /**
     * Config key for {@link #checkers}.
     */
    private static final String KEY_CHECKERS = "checkers";

    /**
     * Config key for {@link #checkerPaths}.
     */
    private static final String KEY_CHECKER_PATHS = "checkerPaths";

    /**
     * The type checkers (processors) to be run.
     */
    private final PropertyEntry<Boolean> useCheckers = 
        createBooleanProperty(KEY_USE_CHECKERS, false);

    /**
     * The type checkers (processors) to be run.
     */
    private final PropertyEntry<String> checkers = 
        createStringProperty(KEY_CHECKERS, "");

    /**
     * The paths needed for the checkers (processors).
     */
    private final PropertyEntry<String> checkerPaths = 
        createStringProperty(KEY_CHECKER_PATHS, "");

    public JavacSettings() {
        super(CATEGORY);
    }

    /**
     * @param useCheckers if the type checkers should be used
     */
    public void setUseCheckers(boolean useCheckers) {
        this.useCheckers.set(useCheckers);
    }

    /**
     * @param checkers the type checkers to use
     */
    public void setCheckers(String checkers) {
        this.checkers.set(checkers);
    }

    /**
     * @param paths the paths on which the type checkers are
     */
    public void setCheckerPaths(String paths) {
        this.checkerPaths.set(paths);
    }

    /**
     * @return true iff the checkers should be used
     */
    public boolean getUseCheckers() {
        return useCheckers.get();
    }

    /**
     * @return all the checkers in a comma separated string
     */
    public String getCheckers() {
        return checkers.get();
    }

    /**
     * @return all checker paths spearated by a colon
     */
    public String getCheckerPaths() {
        return checkerPaths.get();
    }
}
