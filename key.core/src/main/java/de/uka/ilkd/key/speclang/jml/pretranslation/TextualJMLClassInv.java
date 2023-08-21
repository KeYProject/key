/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.ParserRuleContext;


/**
 * A JML class invariant declaration in textual form.
 */
public final class TextualJMLClassInv extends TextualJMLConstruct {
    private final ParserRuleContext inv;
    private final boolean free;

    public TextualJMLClassInv(ImmutableList<JMLModifier> mods, ParserRuleContext inv, String name,
            boolean free) {
        super(mods, name);
        assert inv != null;
        this.inv = inv;
        this.name = name;
        this.free = free;
        setPosition(inv);
    }

    public TextualJMLClassInv(ImmutableList<JMLModifier> mods,
            JmlParser.Class_invariantContext inv, boolean free) {
        this(mods, inv, null, free);
    }

    public ParserRuleContext getInv() {
        return inv;
    }


    @Override
    public String toString() {
        return inv.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLClassInv)) {
            return false;
        }
        TextualJMLClassInv ci = (TextualJMLClassInv) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + inv.hashCode();
    }

    public String getName() {
        return name;
    }

    public boolean isFree() {
        return free;
    }

}
