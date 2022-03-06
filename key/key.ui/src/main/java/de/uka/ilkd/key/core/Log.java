package de.uka.ilkd.key.core;

import ch.qos.logback.classic.filter.ThresholdFilter;
import ch.qos.logback.classic.spi.ILoggingEvent;
import ch.qos.logback.core.Appender;
import de.uka.ilkd.key.ui.Verbosity;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (7/19/21)
 */
public class Log {

    private Log() {}

    /**
     * Global log for simple reason.
     */
    public static final Logger GLOG = LoggerFactory.getLogger("key");

    /**
     * A logger that only prints on the command line. Useful for development,
     * but is forbidden for production code.
     */
    public static final Logger LDEVEL = LoggerFactory.getLogger("key.devel");


    public static void configureLogging(Verbosity verbosity) {
        ch.qos.logback.classic.Logger root = (ch.qos.logback.classic.Logger)
                LoggerFactory.getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME);
        Appender<ILoggingEvent> consoleAppender = root.getAppender("STDOUT");
        var filter = new ThresholdFilter();
        consoleAppender.addFilter(filter);
        filter.setLevel("WARN");
        filter.setLevel(verbosity.name());
    }
}
