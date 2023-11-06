/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic.op;

import java.util.Objects;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Program;
import org.key_project.logic.sort.Sort;

/**
 * This class is used to represent a dynamic logic modality like diamond and box for a target
 * language.
 */
public abstract class Modality extends AbstractSortedOperator<Sort> {
    private final Kind kind;

    protected Modality(Name name, Sort formulaSort, Kind kind) {
        super(name, new Sort[] { formulaSort }, formulaSort, false);
        this.kind = kind;
    }

    public final <K extends Kind> K kind() {
        return (K) kind;
    }

    public abstract Program program();

    public abstract static class Kind implements Named {
        private final Name name;

        public Kind(Name name) {
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
        public boolean equals(Object o) {
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
