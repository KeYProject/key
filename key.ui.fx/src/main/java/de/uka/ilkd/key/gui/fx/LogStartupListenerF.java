/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx;

import de.uka.ilkd.key.settings.PathConfig;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import ch.qos.logback.classic.LoggerContext;
import ch.qos.logback.classic.spi.LoggerContextListener;
import ch.qos.logback.core.Context;
import ch.qos.logback.core.spi.ContextAwareBase;
import ch.qos.logback.core.spi.LifeCycle;

/**
 * Provides the {@code LOG_DIR}
 * {@link PathConfig.KeyPaths#logDirectory} to the {@code logback.xml} configuration of
 * {@code key.ui.fx}.
 * <p>
 * Port of {@code de.uka.ilkd.key.gui.utilities.LoggerStartupListener} in the Swing module
 * {@code key.ui} (that class lives in key.ui and is not visible to this module); the FX
 * {@code logback.xml} needs it so that {@code LogViewF} can tail the per-run log file.
 */
public class LogStartupListenerF extends ContextAwareBase
        implements LoggerContextListener, LifeCycle {
    private boolean started = false;

    @Override
    public void start() {
        if (started) {
            return;
        }
        Context context = getContext();
        context.putProperty("LOG_DIR",
            PathConfig.currentPaths.logDirectory.toAbsolutePath().toString());
        started = true;
    }

    @Override
    public void stop() {
    }

    @Override
    public boolean isStarted() {
        return started;
    }

    @Override
    public boolean isResetResistant() {
        return true;
    }

    @Override
    public void onStart(LoggerContext context) {
    }

    @Override
    public void onReset(LoggerContext context) {
    }

    @Override
    public void onStop(LoggerContext context) {
    }

    @Override
    public void onLevelChange(Logger logger, Level level) {
    }
}
