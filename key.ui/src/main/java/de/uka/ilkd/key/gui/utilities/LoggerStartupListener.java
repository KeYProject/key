/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

// Source - https://stackoverflow.com/a/23969706
// Posted by bhdrk, modified by community. See post 'Timeline' for change history
// Retrieved 2026-07-04, License - CC BY-SA 3.0

import de.uka.ilkd.key.settings.PathConfig;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import ch.qos.logback.classic.LoggerContext;
import ch.qos.logback.classic.spi.LoggerContextListener;
import ch.qos.logback.core.Context;
import ch.qos.logback.core.spi.ContextAwareBase;
import ch.qos.logback.core.spi.LifeCycle;

/// This class provides the `LOG_DIR` [de.uka.ilkd.key.settings.PathConfig.KeyPaths#logDirectory] to
/// the
/// `logback.xml` configuration.
///
/// @author weigl
public class LoggerStartupListener extends ContextAwareBase
        implements LoggerContextListener, LifeCycle {
    private boolean started = false;

    @Override
    public void start() {
        if (started)
            return;
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
