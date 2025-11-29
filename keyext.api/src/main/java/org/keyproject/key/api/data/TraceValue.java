/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

public enum TraceValue implements KeYDataTransferObject {
    /**
     *
     */
    Off,
    /**
     * An error message.
     */
    Error,
    /**
     * A warning message.
     */
    Warning,
    /**
     * An information message.
     */
    Info,
    /**
     * A log message.
     */
    Log,
    /**
     * A debug message.
     *
     * @proposed
     * @since 3.18.0
     */
    Debug
}
