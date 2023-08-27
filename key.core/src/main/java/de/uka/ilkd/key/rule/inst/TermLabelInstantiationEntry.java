/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.util.collection.ImmutableArray;

/**
 *
 *
 */
public class TermLabelInstantiationEntry extends InstantiationEntry<ImmutableArray<TermLabel>> {

    TermLabelInstantiationEntry(ImmutableArray<TermLabel> labels) {
        super(labels);
    }

    /**
     * {@inheritDoc}
     */
    public String toString() {
        String sb = String.valueOf(getInstantiation()) +
                '\n';
        return sb;
    }

}
