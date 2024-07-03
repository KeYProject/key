/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.smt.testgen;

public interface TestGenerationLog {
    public void writeln(String string);

    public void write(String string);

    public void writeException(Throwable t);

    public void testGenerationCompleted();
}
