/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.rifl;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.util.KeYRecoderExcHandler;

import org.slf4j.LoggerFactory;


/**
 * Simple exception handler which just writes to standard output.
 *
 * @author bruns
 */
public class SimpleRIFLExceptionHandler extends KeYRecoderExcHandler {
    static final SimpleRIFLExceptionHandler INSTANCE = new SimpleRIFLExceptionHandler();

    @Override
    public void clear() {}

    @Override
    public List<Throwable> getExceptions() {
        return new ArrayList<>(0);
    }

    @Override
    public void reportException(Throwable e) {
        LoggerFactory.getLogger(SimpleRIFLExceptionHandler.class).error("Error occured!", e);
    }
}
