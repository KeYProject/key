/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.key.cli;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.LoggerContext;
import ch.qos.logback.classic.encoder.PatternLayoutEncoder;
import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.core.ConsoleAppender;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Configures the SLF4J/logback logging of the headless CLI.
 * <p>
 * Replaces any ambient logback configuration (e.g. the logback.xml of other modules on the
 * classpath) so that the CLI always logs to {@code stderr} and keeps {@code stdout} reserved for
 * machine-readable result records (see the {@code KEY_RESULT} protocol).
 */
public final class Log {
    private Log() {
    }

    /**
     * Sets the root log level of the logback context to the given verbosity and routes all log
     * output to {@code stderr}.
     *
     * @param verbosity one of the {@link Verbosity} constants
     */
    public static void configureLogging(int verbosity) {
        if (LoggerFactory.getILoggerFactory() instanceof LoggerContext context) {
            var root = context.getLogger(Logger.ROOT_LOGGER_NAME);
            root.detachAndStopAllAppenders();

            var encoder = new PatternLayoutEncoder();
            encoder.setContext(context);
            encoder.setPattern("%-5level %logger{0} - %msg%n");
            encoder.start();

            var appender = new ConsoleAppender<ILoggingEvent>();
            appender.setContext(context);
            appender.setTarget("System.err");
            appender.setEncoder(encoder);
            appender.start();
            root.addAppender(appender);

            root.setLevel(level(verbosity));
        }
    }

    private static Level level(int verbosity) {
        return switch (verbosity) {
            case Verbosity.SILENT -> Level.OFF;
            case Verbosity.ERROR -> Level.ERROR;
            case Verbosity.INFO -> Level.INFO;
            case Verbosity.DEBUG -> Level.DEBUG;
            case Verbosity.TRACE -> Level.TRACE;
            default -> Level.WARN;
        };
    }
}
