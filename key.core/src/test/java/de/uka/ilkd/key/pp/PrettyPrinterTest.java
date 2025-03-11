/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

class PrettyPrinterTest {
    @Test
    void printLocationVariable() {
        // Test that the pretty printer does not add a ';' when using printFragment.
        // This is important for saving instantiations (see #3071)
        PrettyPrinter pp = PrettyPrinter.purePrinter();
        ProgramElementName name = new ProgramElementName("x");
        LocationVariable variable = new LocationVariable(name, KeYJavaType.VOID_TYPE);
        pp.printFragment(variable);
        Assertions.assertEquals("x", pp.result());
    }
}
