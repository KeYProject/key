/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import java.util.Objects;

import org.key_project.logic.*;
import org.key_project.logic.sort.Sort;

import org.jspecify.annotations.Nullable;

/// This class is used to represent a dynamic logic modality like diamond and box for a target
/// language.
public abstract class Modality extends AbstractSortedOperator {
    private final Kind kind;

    protected Modality(Name name, Sort formulaSort, Kind kind) {
        super(name, new Sort[] { formulaSort }, formulaSort, Modifier.NONE);
        this.kind = kind;
    }

    /// The kind of this modality, e.g., box, diamond.
    ///
    /// @return The kind of the modality.
    /// @param <K> Restricts the expected type of the kind.
    public final <K extends Kind> K kind() {
        return (K) kind;
    }

    /// The program contained in this modality.
    ///
    /// @return the program.
    public abstract Program programBlock();

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> kind;
        case 1 -> programBlock();
        default -> throw new IndexOutOfBoundsException(
            "Modality " + name() + " has only two children");
        };
    }

    /// Modality kinds like box and diamond.
    public abstract static class Kind implements Named, TerminalSyntaxElement {
        private final Name name;

        protected Kind(Name name) {
            this.name = name;
        }

        @Override
        public Name name() {
            return name;
        }

        @Override
        public String toString() {
            return name().toString();
        }

        @Override
        public boolean equals(@Nullable Object o) {
            if (this == o)
                return true;
            if (!(o instanceof Kind kind))
                return false;
            return Objects.equals(name(), kind.name());
        }

        @Override
        public int hashCode() {
            return Objects.hash(name());
        }
    }
}
