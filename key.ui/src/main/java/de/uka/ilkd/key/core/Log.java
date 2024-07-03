/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.core;

import de.uka.ilkd.key.ui.Verbosity;

import ch.qos.logback.classic.Level;
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
     * A logger that only prints on the command line. Useful for development,
     * but is forbidden for production code.
     */
    public static final Logger LDEVEL = LoggerFactory.getLogger("key.devel");


    public static void configureLogging(int verbosity) {
        ch.qos.logback.classic.Logger root = (ch.qos.logback.classic.Logger) LoggerFactory
                .getLogger(org.slf4j.Logger.ROOT_LOGGER_NAME);
        switch (verbosity) {
        case Verbosity.TRACE:
            root.setLevel(Level.TRACE);
            break;
        case Verbosity.DEBUG:
            root.setLevel(Level.DEBUG);
            break;
        case Verbosity.INFO:
            root.setLevel(Level.INFO);
            break;
        case Verbosity.NORMAL:
            root.setLevel(Level.ERROR);
            break;
        case Verbosity.SILENT:
            root.setLevel(Level.OFF);
            break;
        }
    }
}
