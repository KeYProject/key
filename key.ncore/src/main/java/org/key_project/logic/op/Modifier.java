/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.key_project.logic.Name;
import org.key_project.logic.Named;

/**
 * A modifier for a {@link Function} and similar elements. Defines additional properties for
 * operators in a more flexible manner than fields.
 */
public class Modifier implements Named {
    private final int bitMask;

    private final Name name;

    private static final Map<Integer, Modifier> MODIFIERS = new ConcurrentHashMap<>();

    /**
     * No modifiers.
     */
    public static final Modifier NONE = new Modifier("none", 0);

    /**
     * A rigid (non-flexible) function.
     */
    public static final Modifier RIGID = new Modifier("rigid", 1);

    /**
     * A skolem function.
     */
    public static final Modifier SKOLEM = new Modifier("skolem", 1 << 1);

    /**
     * A unique function.
     */
    public static final Modifier UNIQUE = new Modifier("unique", 1 << 2);

    protected Modifier(String name, int bitMask) {
        if (MODIFIERS.containsKey(bitMask)) {
            throw new IllegalArgumentException(
                "Modifier with bitmask '" + bitMask + "' already declared with name: "
                    + MODIFIERS.get(bitMask).name);
        }
        this.bitMask = bitMask;
        this.name = new Name(name);
        MODIFIERS.put(bitMask, this);
    }

    private Modifier(int bitMask) {
        name = new Name("Combined(" + bitMask + ")");
        this.bitMask = bitMask;
    }

    @Override
    public Name name() {
        return name;
    }

    /**
     * Creates a new combined modifier.
     *
     * @param that The midifier to add to the current one.
     * @return A modifier that has all properties of `this` and `that`.
     */
    public Modifier combine(Modifier that) {
        return new Modifier(bitMask | that.bitMask);
    }

    /**
     * Checks whether `m` is a subset of the current modifier.
     *
     * @param m The bitmask to check against.
     * @return Whether all set bits of `m` are also set on `this`.
     */
    public boolean match(Modifier m) {
        return (bitMask & m.bitMask) != 0;
    }
}
