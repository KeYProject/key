/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Objects;

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NullMarked;


/**
 * A JML adt declaration in textual form.
 */
@NullMarked
public final class TextualJMLDatatype extends TextualJMLConstruct {
    private final LabeledParserRuleContext adt;

    /**
     * new textual representation.
     *
     * @param adt the expression in this clause
     */
    public TextualJMLDatatype(LabeledParserRuleContext adt) {
        super(ImmutableSLList.nil());
        this.adt = Objects.requireNonNull(adt);
        setPosition(adt);
    }

    public LabeledParserRuleContext getAdt() {
        return adt;
    }


    @Override
    public String toString() {
        return adt.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass())
            return false;

        TextualJMLDatatype that = (TextualJMLDatatype) o;
        return adt.equals(that.adt);
    }

    @Override
    public int hashCode() {
        return adt.hashCode();
    }
}
