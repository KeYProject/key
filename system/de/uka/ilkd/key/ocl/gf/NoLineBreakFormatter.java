// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.ocl.gf;

import java.util.logging.Formatter;
import java.util.logging.LogRecord;

/**
 * @author daniels
 * A simple Formatter class, that does not introduce linebreaks, so that
 * continous lines can be read under each other.
 */
public class NoLineBreakFormatter extends Formatter {

        /** 
         * @see java.util.logging.Formatter#format(java.util.logging.LogRecord)
         */
        public String format(LogRecord record) {
                final String shortLoggerName = record.getLoggerName().substring(record.getLoggerName().lastIndexOf('.') + 1);
                return record.getLevel() + " : "
                + shortLoggerName + " "
                + record.getSourceMethodName() + " -:- "
                + record.getMessage() + "\n";
        }
}
