/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.convenience;

import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;

/**
 * A tree walker that allows to customize the traversal. The walker can report elements during
 * ascending, and may skip the traversal of certain subtrees on demand.
 *
 * @author AL
 */
public class CustomTreeWalker extends TreeWalker {

    boolean isReportingReturns = false;

    ModelElementFilter childFilter = null;

    ModelElementFilter parentFilter = null;

    boolean isReturning = false;

    protected CustomTreeWalker(int initialStackCapacity) {
        super(initialStackCapacity);
    }

    public CustomTreeWalker(ProgramElement root) {
        super(root);
    }

    public CustomTreeWalker(ProgramElement root, int initialStackCapacity) {
        super(root, initialStackCapacity);
    }

    /**
     * Checks whether non terminal elements are reported when returning from recursion. Default is
     * false (no report).
     */
    public boolean isReportingReturns() {
        return isReportingReturns;
    }

    /**
     * Decide whether non terminal elements should be reported when returning from recursion.
     */
    public void setReportingReturns(boolean yes) {
        isReportingReturns = yes;
    }

    /**
     * Returns true if the current element is left. This element will not be reported any longer. If
     * return reporting is switched off, only terminal elements will be reported as returning.
     *
     * @see #isReportingReturns
     */
    public boolean isReturning() {
        return isReturning;
    }

    /**
     * Set a filter that decides whether the children of a non terminal should be reported, or not.
     * This setting takes effect beginning at the next call to {@link #next()}. It does not affect
     * reports of returning nodes.
     */
    public void setParentFilter(ModelElementFilter filter) {
        parentFilter = filter;
    }

    // only enter children that are accepted by the given filter
    // this setting takes effect from now on
    // does not affect reports of returning nodes
    public void setChildFilter(ModelElementFilter filter) {
        childFilter = filter;
    }

    public boolean next() {
        if (count == 0) {
            current = null;
            isReturning = true;
            return false;
        }
        current = stack[--count]; // pop
        if (current == null) { // end marker
            if (isReportingReturns) {
                current = stack[--count]; // report corresponding entry
                isReturning = true;
                return true;
            } else {
                do {
                    count -= 1; // skip element that we are returning from
                    if (count == 0) {
                        current = null;
                        isReturning = true;
                        return false;
                    }
                    current = stack[--count]; // pop
                } while (current == null);
            }
        }
        if (current instanceof NonTerminalProgramElement) {
            NonTerminalProgramElement nt = (NonTerminalProgramElement) current;
            int s = nt.getChildCount();
            if (count + s + 2 >= stack.length) {
                ProgramElement[] newStack =
                    new ProgramElement[Math.max(stack.length * 2, count + s + 2)];
                System.arraycopy(stack, 0, newStack, 0, count);
                stack = newStack;
            }
            stack[count++] = nt; // push back
            stack[count++] = null; // mark as end
            if (parentFilter == null || parentFilter.accept(nt)) {
                if (childFilter == null) {
                    for (int i = s - 1; i >= 0; i -= 1) {
                        stack[count++] = nt.getChildAt(i); // push
                    }
                } else {
                    for (int i = s - 1; i >= 0; i -= 1) {
                        ProgramElement e = nt.getChildAt(i);
                        if (childFilter.accept(e)) {
                            stack[count++] = e;
                        }
                    }
                }
            }
            isReturning = false;
        } else {
            isReturning = true; // report terminal elements only once
        }
        return true;
    }
}
