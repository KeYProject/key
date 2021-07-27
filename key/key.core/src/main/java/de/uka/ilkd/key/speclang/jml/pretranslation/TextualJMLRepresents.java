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

import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import org.key_project.util.collection.ImmutableList;

/**
 * A JML represents clause in textual form.
 */
public final class TextualJMLRepresents extends TextualJMLConstruct {

    private final LabeledParserRuleContext represents;


    public TextualJMLRepresents(ImmutableList<String> mods, LabeledParserRuleContext represents) {
        super(mods);
        assert represents != null;
        this.represents = represents;
        setPosition(represents);
    }

    public TextualJMLRepresents(ImmutableList<String> mods, LabeledParserRuleContext represents, String name) {
        this(mods, represents);
        this.name = name;
    }

    public LabeledParserRuleContext getRepresents() {
        return represents;
    }

    @Override
    public String toString() {
        return represents.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLRepresents)) {
            return false;
        }
        TextualJMLRepresents r = (TextualJMLRepresents) o;
        return mods.equals(r.mods) && represents.equals(r.represents);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + represents.hashCode();
    }

    public String getName() {
        return name;
    }
}