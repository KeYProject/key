/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import javax.annotation.Nonnull;

import de.uka.ilkd.key.logic.ChoiceExpr;
import de.uka.ilkd.key.logic.Name;


/**
 * Provides a unique key for taclets based on a taclet's name and its taclet options. This class is
 * e.g. used by the parser which might encounter more than one taclet of the same name (but with
 * different taclet options).
 *
 * One does not need to use this implementation (but can rely on a taclet's own
 * {@link Taclet#equals(Object)} and {@link Taclet#hashCode()} method.
 */
public class RuleKey {
    public final @Nonnull Name name;
    public final @Nonnull ChoiceExpr choices;
    public final Rule r;

    RuleKey(@Nonnull Name name, @Nonnull ChoiceExpr choices, Rule r) {
        this.name = name;
        this.choices = choices;
        this.r = r;
    }

    public RuleKey(Rule r) {
        this(r.name(), (r instanceof Taclet ? ((Taclet) r).getChoices() : ChoiceExpr.TRUE), r);
    }

    public boolean equals(Object o) {
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
