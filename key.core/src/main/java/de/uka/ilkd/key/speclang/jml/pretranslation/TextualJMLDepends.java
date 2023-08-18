/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml.pretranslation;

import java.util.LinkedHashMap;
import java.util.Map;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;


/**
 * A JML depends / accessible clause for a model field in textual form. Note that such clauses for
 * *methods* are part of TextualJMLSpecCase.
 */
public final class TextualJMLDepends extends TextualJMLConstruct {
    private final Map<Name, ImmutableList<LabeledParserRuleContext>> depends =
        new LinkedHashMap<>();

    public TextualJMLDepends(ImmutableList<JMLModifier> mods, Name[] heaps,
            @Nonnull LabeledParserRuleContext depends) {
        super(mods);
        setPosition(depends);
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
