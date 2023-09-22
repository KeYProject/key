/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.core;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.attribute.FileTime;
import java.time.Duration;
import java.time.Instant;
import java.time.temporal.ChronoUnit;
import javax.annotation.Nullable;

import de.uka.ilkd.key.settings.PathConfig;
import de.uka.ilkd.key.ui.Verbosity;

import ch.qos.logback.classic.filter.ThresholdFilter;
import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.core.Appender;
import ch.qos.logback.core.FileAppender;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (7/19/21)
 */
public class Log {
    /**
     * Global log for simple reason.
     */
    public static final Logger GLOG = LoggerFactory.getLogger("key");

    /**
     * A logger that only prints on the command line. Useful for development, but is forbidden for
     * production code.
     */
    public static final Logger LDEVEL = LoggerFactory.getLogger("key.devel");

    private static final Logger LOGGER = LoggerFactory.getLogger(Log.class);

    public static Path getCurrentLogFile() {
        ch.qos.logback.classic.Logger root =
            (ch.qos.logback.classic.Logger) LoggerFactory
                    .getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME);
        FileAppender<?> fileAppend = (FileAppender<?>) root.getAppender("FILE");
        return Paths.get(fileAppend.getFile());
    }

    public static void configureLogging(@Nullable Integer verbosity) {
        Runtime.getRuntime().addShutdownHook(new Thread(Log::cleanOldLogFiles));
        ch.qos.logback.classic.Logger root = (ch.qos.logback.classic.Logger) LoggerFactory
                .getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME);
        if (verbosity != null) {
            Appender<ILoggingEvent> consoleAppender = root.getAppender("STDOUT");
            consoleAppender.clearAllFilters();
            var filter = new ThresholdFilter();
            consoleAppender.addFilter(filter);
            switch (verbosity.byteValue()) {
            case Verbosity.TRACE:
                filter.setLevel("TRACE");
                break;
            case Verbosity.DEBUG:
                filter.setLevel("DEBUG");
                break;
            case Verbosity.INFO:
                filter.setLevel("INFO");
                break;
            case Verbosity.NORMAL:
                filter.setLevel("ERROR");
                break;
            case Verbosity.SILENT:
                filter.setLevel("OFF");
                break;
            default:
                filter.setLevel("WARN");
                break;
            }
            filter.start();
        }
    }

    private static void cleanOldLogFiles() {
        var logDir = PathConfig.getLogDirectory().toPath();
        try (var files = Files.list(logDir)) {
            var duration = Duration.of(14, ChronoUnit.DAYS);
            var refDate = Instant.now().minus(duration);

            files.forEach(file -> {
                try {
                    var creationTime = (FileTime) Files.getAttribute(file, "creationTime");
                    var dt = creationTime.toInstant();
                    if (dt.isBefore(refDate)) {
                        LOGGER.info("Log file {} is marked for delete as it is older than {} days.",
                            file, duration);
                        Files.delete(file);
                    }
                } catch (IOException e) {
                    LOGGER.error("Could not delete log file {}", file, e);
                }
            });
        } catch (IOException e) {
            LOGGER.error("Could not read logging directory", e);
        }
    }
}
