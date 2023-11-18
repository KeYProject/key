/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;


import java.util.List;
import java.util.Objects;

import org.jspecify.annotations.NonNull;

/**
 * A choice is an option in a category.
 * <p>
 * A choice is represented by a string, where the category is separated by the option with a colon.
 * <p>
 * Choices can be declared within KeY files. They influence the activation of taclets.
 *
 * @see de.uka.ilkd.key.nparser.ParsingFacade#getChoices(List)
 */
public class Choice implements Named {
    private final @NonNull Name name;
    private final @NonNull String category;

    /**
     * Creates a choice object with name {@code <category>:<choice>}.
     */
    public Choice(String choice, String category) {
        this(new Name(category + ":" + choice), category);
    }

    public Choice(@NonNull Name name, @NonNull String category) {
        this.name = name;
        this.category = category;
    }


    @Override
    public @NonNull Name name() {
        return name;
    }

    public @NonNull String category() {
        return category;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        Choice choice = (Choice) o;
        return name.equals(choice.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }

    @Override
    public String toString() {
        return name.toString();
    }
}
