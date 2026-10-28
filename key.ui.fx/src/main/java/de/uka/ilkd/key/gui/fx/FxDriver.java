/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import javafx.stage.Stage;

/**
 * A standalone view driver used during development and automated verification (milestone M2): if
 * the system property {@code key.fx.driver} names a class, that class receives the primary stage
 * instead of the full {@link MainWindowF}. A driver typically shows a single view together with a
 * local {@code KeYSelectionModel} and a demo proof loaded via the core {@code KeYEnvironment},
 * which allows per-view verification without the full main window.
 * <p>
 * Drivers are development scaffolding; they may be removed once the views are integrated and
 * verified in the main window.
 */
@FunctionalInterface
public interface FxDriver {

    /**
     * Builds and shows the driver UI on the given stage.
     *
     * @param stage the primary stage of the JavaFX application
     * @throws Exception on any setup error (reported by the launcher)
     */
    void start(Stage stage) throws Exception;
}
