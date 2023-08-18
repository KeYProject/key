/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import java.util.List;

import recoder.java.CompilationUnit;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * Walks all syntax trees from a list of compilation units in depth-first order.
 *
 * @author AL
 */
public class ForestWalker extends AbstractTreeWalker {

    final List<CompilationUnit> unitList;

    int unitIndex;

    public ForestWalker(List<CompilationUnit> units) {
        super(units.size() * 8);
        this.unitList = units;
        unitIndex = 0;
        if (unitList.size() > 0) {
            reset(unitList.get(unitIndex));
        }
    }

    public boolean next() {
        if (count == 0) {
            current = null;
            if (unitIndex >= unitList.size() - 1) {
                return false;
            }
            unitIndex += 1;
            reset(unitList.get(unitIndex));
            return next();
        }
        current = stack[--count]; // pop
        if (current instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) current;
            int s = nt.getChildCount();
            if (count + s >= stack.length) {
                ProgramElement[] newStack =
                    new ProgramElement[Math.max(stack.length * 2, count + s)];
                System.arraycopy(stack, 0, newStack, 0, count);
                stack = newStack;
            }
            for (int i = s - 1; i >= 0; i -= 1) {
                stack[count++] = nt.getChildAt(i); // push
            }
        }
        return true;
    }

    public boolean equals(Object x) {
        if (!(x instanceof ForestWalker)) {
            return false;
        }
        ForestWalker fw = (ForestWalker) x;
        if (!super.equals(x)) {
            return false;
        }
        return (fw.unitIndex == unitIndex && fw.unitList.equals(unitList));
    }

}
