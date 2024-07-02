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

package de.uka.ilkd.key.util;

/**
 * This interface provides the class Debug with the possibility
 * to be administrated from within management tools such as 
 * "jconsole". Debugging can be switched on / off dynamically using
 * a mangement console. Also the set of traced classes can be 
 * changed
 *
 * @author mulbrich
 */
public interface DebugMBean {

    /**
     * set the current debug state. If set to true, debug messages 
     * are printed to stdout.
     *
     * @param debug the new debug state to set
     */
    public void setDebugState(boolean debug);

    /**
     * get the current debug state. If true, messages are printed,
     * if false, no message gets printed.
     *
     * @return the current debug state
     */
    public boolean getDebugState();

    /**
     * get the list of prefixes for which messages are shown. 
     * Every message is prefixed with the class name that
     * triggered it. Only if the classname begins with one entry
     * of this list, the message will be displayed-
     *
     * @return a ":"-separated list of prefixes
     */
    public String getShowOnlyPrefixes();

    /**
     * set the list of prefixes for which messages are shown. 
     * Every message is prefixed with the class name that
     * triggered it. Only if the classname begins with one entry
     * of this list, the message will be displayed-
     *
     * @param showOnlyPrefixes a ":"-separated list of prefixes
     */
    public void setShowOnlyPrefixes(String showOnlyPrefixes);

}