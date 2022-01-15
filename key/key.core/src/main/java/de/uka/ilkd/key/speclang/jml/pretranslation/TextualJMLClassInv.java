// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.jml.pretranslation;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.key_project.util.collection.ImmutableList;

import java.util.Objects;


/**
 * A JML class invariant declaration in textual form.
 */
public final class TextualJMLClassInv extends TextualJMLConstruct {
    private final JmlParser.Class_invariantContext inv;

    public TextualJMLClassInv(ImmutableList<String> mods, JmlParser.Class_invariantContext ctx) {
        super(mods, null);
        inv = Objects.requireNonNull(ctx);
    }

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
        if (!(o instanceof TextualJMLClassInv)) {
            return false;
        }
        TextualJMLClassInv ci = (TextualJMLClassInv) o;
        return mods.equals(ci.mods) && inv.equals(ci.inv);
    }


    @Override
    public int hashCode() {
        return Objects.hash(mods, inv);
    }
}