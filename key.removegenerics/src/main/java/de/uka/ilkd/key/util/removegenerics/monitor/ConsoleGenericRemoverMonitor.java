package de.uka.ilkd.key.util.removegenerics.monitor;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ConsoleGenericRemoverMonitor implements GenericRemoverMonitor {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ConsoleGenericRemoverMonitor.class);

    @Override
    public void taskStarted(String message) {
        LOGGER.info(message);
    }

    @Override
    public void warningOccurred(String message) {
        LOGGER.warn(message);
    }
}
