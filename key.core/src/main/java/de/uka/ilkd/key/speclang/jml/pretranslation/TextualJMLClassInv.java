/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.Objects;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;

/**
 * A JML class invariant declaration in textual form.
 */
public final class TextualJMLClassInv extends TextualJMLConstruct {
    private final JmlParser.Class_invariantContext inv;
    private final boolean free;

    public TextualJMLClassInv(ImmutableList<JMLModifier> mods,
            JmlParser.Class_invariantContext ctx, String name, boolean free) {
        super(mods, null);
        inv = Objects.requireNonNull(ctx);
        setPosition(ctx);
        this.name = name;
        this.free = free;
    }

    public TextualJMLClassInv(ImmutableList<JMLModifier> modifiers,
            JmlParser.Class_invariantContext inv, boolean free) {
        this(modifiers, inv, null, free);
    }

    /**
     * User-defined name of the class invariant.
     */
    public String getName() {
        if (name == null && inv.entity_name() != null) {
            name = inv.entity_name().ident().getText();
        }
        return name;
    }

    public LabeledParserRuleContext getInv() {
        return new LabeledParserRuleContext(inv, createTermLabel(
            OriginTermLabel.SpecType.INVARIANT,
            inv.start, getName()));
    }


    @Override
    public String toString() {
        return inv.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLClassInv ci)) {
            return false;
        }
        return modifiers.equals(ci.modifiers) && inv.equals(ci.inv);
    }


    @Override
    public int hashCode() {
        return Objects.hash(modifiers, inv);
    }

    public String getName() {
        return name;
    }

    public boolean isFree() {
        return free;
    }

}
