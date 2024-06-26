/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import org.key_project.logic.Name;

import org.jspecify.annotations.NullMarked;

/**
 * A label that is associated with the name of a term.
 * This name can be origin from the JML specification.
 *
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
@NullMarked
public record SpecNameLabel(String label) implements TermLabel {
    public static final Name NAME = new Name("name");

    public static TermLabelFactory<?> getFactory() {
        return (TermLabelFactory<TermLabel>) (arguments, services) -> new SpecNameLabel(arguments.get(0));
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getTLChild(int i) {
        if (i == 0)
            return label;
        throw new IllegalArgumentException("index out of bounds");
    }

    @Override
    public int getTLChildCount() {
        return 1;
    }

    @Override
    public boolean isProofRelevant() {
        return false;
    }

    @Override
    public String toString() {
        return "name(\"" + label + "\")";
    }
}
