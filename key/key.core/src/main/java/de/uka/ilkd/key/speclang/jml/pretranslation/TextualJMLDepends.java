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

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import javax.annotation.Nonnull;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.util.LinkedHashMap;
import java.util.Map;


/**
 * A JML depends / accessible clause for a model field in textual form.
 * Note that such clauses for *methods* are part of TextualJMLSpecCase.
 */
public final class TextualJMLDepends extends TextualJMLConstruct {
    private Map<Name, ImmutableList<LabeledParserRuleContext>> depends = new LinkedHashMap<>();

    public TextualJMLDepends(ImmutableList<String> mods, Name[] heaps, @Nonnull LabeledParserRuleContext depends) {
        super(mods);
        for (Name hName : HeapLDT.VALID_HEAP_NAMES) {
            this.depends.put(hName, ImmutableSLList.nil());
        }

        for (Name heap : heaps) {
            this.depends.put(heap, ImmutableSLList.singleton(depends));
        }
    }

    public ImmutableList<LabeledParserRuleContext> getDepends() {
        return depends.get(HeapLDT.BASE_HEAP_NAME);
    }

    public ImmutableList<LabeledParserRuleContext> getDepends(Name hName) {
        return depends.get(hName);
    }

    @Override
    public String toString() {
        return depends.toString();
    }


    @Override
    public boolean equals(Object o) {
        if (!(o instanceof TextualJMLDepends)) {
            return false;
        }
        TextualJMLDepends a = (TextualJMLDepends) o;
        return mods.equals(a.mods) && depends.equals(a.depends);
    }


    @Override
    public int hashCode() {
        return mods.hashCode() + depends.hashCode();
    }
}