package de.uka.ilkd.key.gui;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This is a handy class for tracing Exceptions that are otherwise lost in the thread chaos. See the
 * method handleException() in class java.awt.EventDispatchThread. The magic system property
 * "sun.awt.exception.handler" must be set to "de.uka.ilkd.key.gui.ExceptionalHandler" for this to
 * work.
 */

public class ExceptionalHandler {
    public void handle(Throwable t) {
        Logger log = LoggerFactory.getLogger(ExceptionalHandler.class);
        log.error("*** Here's the exceptional handler ***", t);
    }
}
