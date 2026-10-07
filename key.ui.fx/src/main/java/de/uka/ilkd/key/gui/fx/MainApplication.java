/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import javafx.application.Application;
import javafx.stage.Stage;

/**
 * The JavaFX application of KeY, counter-part of {@code de.uka.ilkd.key.gui.MainWindow} in the
 * Swing module {@code key.ui}.
 * <p>
 * Since milestone M1 the application delegates to the fully-fledged {@link MainWindowF}: docking
 * workspace with the default layout, menu bar, toolbars, themed status bar and notifications.
 * <p>
 * For development and automated verification, the system property {@code key.fx.driver} may name
 * an {@link FxDriver} class which receives the primary stage instead of the main window.
 */
public final class MainApplication extends Application {

    @Override
    public void start(final Stage stage) throws Exception {
        String driverName = System.getProperty("key.fx.driver");
        if (driverName != null && !driverName.isBlank()) {
            Class<?> driverClass = Class.forName(driverName);
            FxDriver driver = (FxDriver) driverClass.getDeclaredConstructor().newInstance();
            driver.start(stage);
            return;
        }
        new MainWindowF(stage).initialize();
    }
}
