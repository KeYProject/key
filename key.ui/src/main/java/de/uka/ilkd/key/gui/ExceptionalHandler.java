// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This is a handy class for tracing Exceptions that are otherwise lost in
 * the thread chaos. See the method handleException() in
 * class java.awt.EventDispatchThread. The magic system property
 * "sun.awt.exception.handler" must be set to
 * "de.uka.ilkd.key.gui.ExceptionalHandler" for this to work.
 */

public class ExceptionalHandler {
    public void handle(Throwable t) {
        Logger log = LoggerFactory.getLogger(ExceptionalHandler.class);
        log.error("*** Here's the exceptional handler ***", t);
    }
}