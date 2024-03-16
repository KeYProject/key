/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.smt.testgen;

import static de.uka.ilkd.key.testgen.template.Constants.NEW_LINE;

/**
 * Implementation of {@link TestGenerationLogger} which stores the log in memory.
 *
 * @author Martin Hentschel
 */
public class MemoryTestGenerationLogger implements TestGenerationLogger {
    /**
     * The {@link StringBuffer} which stores all the content.
     */
    private final StringBuffer sb = new StringBuffer();

    /**
     * {@inheritDoc}
     */
    @Override
    public void writeln(String message) {
        sb.append(message);
        sb.append(NEW_LINE);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void writeException(Throwable throwable) {
        sb.append(throwable.getMessage());
        sb.append(NEW_LINE);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void close() {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return sb.toString();
    }
}
