/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule;

import org.key_project.logic.ChoiceExpr;
import org.key_project.logic.Name;
import org.key_project.prover.rules.Rule;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;


/**
 * Provides a unique key for taclets based on a taclet's name and its taclet options. This class is
 * e.g. used by the parser which might encounter more than one taclet of the same name (but with
 * different taclet options).
 *
 * One does not need to use this implementation (but can rely on a taclet's own
 * {@link Taclet#equals(Object)} and {@link Taclet#hashCode()} method.
 */
@NullMarked
public class RuleKey {
    public final Name name;
    public final ChoiceExpr choices;
    public final Rule r;

    RuleKey(Name name, ChoiceExpr choices, Rule r) {
        this.name = name;
        this.choices = choices;
        this.r = r;
    }

    public RuleKey(Rule r) {
        this(r.name(), (r instanceof Taclet ? ((Taclet) r).getChoices() : ChoiceExpr.TRUE), r);
    }

    public boolean equals(@Nullable Object o) {
        if (o == null) {
            return false;
        }
        if (o == this) {
            return true;
        }

        if (o.getClass() != this.getClass()) {
            return false;
        }

        final RuleKey other = (RuleKey) o;
        return name.equals(other.name) && choices.equals(other.choices);
    }

    public int hashCode() {
        return name.hashCode() * 17 + 7 * choices.hashCode();
    }

    public String toString() {
        return "(" + name + ", " + choices + ")";
    }

}
