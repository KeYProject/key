/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen.smt.testgen;

public interface TestGenerationLog {
    void writeln(String string);

    void write(String string);

    void writeException(Throwable t);

    void testGenerationCompleted();
}