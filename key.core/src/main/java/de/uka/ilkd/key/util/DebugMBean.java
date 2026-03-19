/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util;

/**
 * This interface provides the class Debug with the possibility to be administrated from within
 * management tools such as "jconsole". Debugging can be switched on / off dynamically using a
 * mangement console. Also the set of traced classes can be changed
 *
 * @author mulbrich
 */
public interface DebugMBean {

    /**
     * set the current debug state. If set to true, debug messages are printed to stdout.
     *
     * @param debug the new debug state to set
     */
    void setDebugState(boolean debug);

    /**
     * get the current debug state. If true, messages are printed, if false, no message gets
     * printed.
     *
     * @return the current debug state
     */
    boolean getDebugState();

    /**
     * get the list of prefixes for which messages are shown. Every message is prefixed with the
     * class name that triggered it. Only if the classname begins with one entry of this list, the
     * message will be displayed-
     *
     * @return a ":"-separated list of prefixes
     */
    String getShowOnlyPrefixes();

    /**
     * set the list of prefixes for which messages are shown. Every message is prefixed with the
     * class name that triggered it. Only if the classname begins with one entry of this list, the
     * message will be displayed-
     *
     * @param showOnlyPrefixes a ":"-separated list of prefixes
     */
    void setShowOnlyPrefixes(String showOnlyPrefixes);

}
