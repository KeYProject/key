/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.smt.model;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents a sequence in an SMT model.
 *
 * @author mihai
 *
 */
@NullMarked
public class Sequence {
    /**
     * The name of the sequence.
     */
    private String name;
    /**
     * The values contained by the sequence.
     */
    private @Nullable String[] content;

    /**
     * The content array is deliberately left {@code null} for negative lengths and filled in later;
     * the initialization check cannot verify the deliberately unset {@code @Nullable} array, so the
     * difference is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:initialization.fields.uninitialized")
    public Sequence(int length, String name) {
        super();
        this.name = name;
        if (length >= 0) {
            content = new String[length];
        }
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int getLength() {
        return content.length;
    }

    /**
     * Returns the value stored at the given index; entries may be <code>null</code> before they
     * have been set for a freshly extracted sequence (cf. {@link #set(int, String)}).
     */
    public @Nullable String get(int i) {
        return content[i];
    }

    public void set(int i, @Nullable String s) {
        content[i] = s;
    }

    public String toString() {
        StringBuilder result = new StringBuilder("Seq: " + name + "\n");
        result.append("Length: ").append(content.length).append("\n");

        for (int i = 0; content != null && i < content.length; ++i) {

            result.append("[").append(i).append("] = ").append(content[i]).append("\n");
        }
        return result.toString();
    }

}
