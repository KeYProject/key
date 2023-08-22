/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.label;

import de.uka.ilkd.key.logic.Name;


/**
 * A label that is associated with the name of a term.
 * This name can be origin from the JML specification.
 *
 * @author Alexander Weigl
 * @version 1 (1/15/22)
 */
public class SpecNameLabel implements TermLabel {
    public static final Name NAME = new Name("name");

    private final String label;

    public SpecNameLabel(String label) {
        this.label = label;
    }

    public static TermLabelFactory<?> getFactory() {
        return (TermLabelFactory<TermLabel>) (arguments,
                services) -> new SpecNameLabel(arguments.get(0));
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public Object getChild(int i) {
        if (i == 0)
            return label;
        throw new IllegalArgumentException("index out of bounds");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    public String getLabel() {
        return label;
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
