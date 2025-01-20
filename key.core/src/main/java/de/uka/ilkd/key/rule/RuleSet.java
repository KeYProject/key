/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import org.key_project.logic.Name;
import org.key_project.logic.Named;

/**
 * this class represents a heuristic. Taclets can belong to different heuristics and are executed
 * automatic if these are selected. A heuristic is just a name.
 */
public record RuleSet(Name name) implements Named {
    /**
     * creates a heuristic
     *
     * @param name Name object that contains name of the heuristic
     */
    public RuleSet {
    }

    /**
     * gets name of the heuristic
     *
     * @return Name object that is the name of the heuristic
     */
    @Override
    public Name name() {
        return name;
    }

    public int hashCode() {
        return 3 * name().hashCode();
    }

    /**
     * returns true it the o is the same object as this
     */
    public boolean equals(Object o) {
        if (o instanceof RuleSet) {
            return this.name().equals(((RuleSet) o).name());
        }
        return false;
    }


    /**
     * toString
     */
    public String toString() {
        return name.toString();
    }
}
