/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.JavaProgramElement;
import de.uka.ilkd.key.java.ast.ProgramElement;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class ProgramElementReplacer extends CreatingASTVisitor {

    private ProgramElement oldElement;
    private ProgramElement newElement;
    private boolean done;

    /**
     * The elements to replace are supplied per call to {@link #replace(ProgramElement,
     * ProgramElement)}; the constructor cannot assign them, so the difference is suppressed with a
     * scoped key.
     */
    @SuppressWarnings("nullness:initialization.fields.uninitialized")
    public ProgramElementReplacer(JavaProgramElement program, Services services) {
        super(program, false, services);
    }

    /**
     * Replaces the old top-level element by the given replacement element.
     * <p>
     * The element to replace is present whenever a replacement is requested; the dereference of
     * the (nullable) element is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public ProgramElement replace(ProgramElement oldElement, ProgramElement newElement) {
        this.oldElement = oldElement;
        this.newElement = newElement;
        done = false;
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        ProgramElement result = el.get(ProgramElement.class);
        if (result == null) {
            throw new IllegalStateException("The element to replace was not found in the program");
        }
        return result;
    }

    protected void doAction(ProgramElement element) {
        if (!done && element == oldElement) {
            done = true;
            addChild(newElement);
            changed();
        } else {
            super.doAction(element);
        }
    }

}
