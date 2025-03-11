/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
