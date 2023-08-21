/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.speclang.njml.JmlParser;

import org.key_project.util.collection.ImmutableList;

/**
 * A JML field declaration (ghost or model) in textual form.
 */
public final class TextualJMLFieldDecl extends TextualJMLConstruct {

    private final JmlParser.Field_declarationContext decl;


    public TextualJMLFieldDecl(ImmutableList<JMLModifier> mods,
            JmlParser.Field_declarationContext decl) {
        super(mods);
        assert decl != null;
        this.decl = decl;
        setPosition(decl);
    }


    public JmlParser.Field_declarationContext getDecl() {
        return decl;
    }


    @Override
    public String toString() {
        return decl.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLFieldDecl)) {
            return false;
        }
        TextualJMLFieldDecl fd = (TextualJMLFieldDecl) o;
        return mods.equals(fd.mods) && decl.equals(fd.decl);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + decl.hashCode();
    }
}
