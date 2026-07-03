/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

/**
 * A map key wrapping a {@link JTerm} with <em>label-sensitive</em> equality. Since
 * {@link JTerm#equals(Object)} ignores term labels, caches whose values depend on the labels of
 * the keyed term must not conflate label variants; wrapping the key in this record restores the
 * distinction via {@link JTerm#equalsIncludingLabels(Object)}.
 *
 * <p>
 * The hash code is the term's {@link JTerm#labeledHashCode() label-sensitive} hash code, so label
 * variants land in different buckets just as they did when term equality itself was
 * label-sensitive.
 * </p>
 *
 * @param term the term to use as a label-sensitive key (must not be null)
 */
public record StrictTermKey(JTerm term) {
    @Override
    public boolean equals(Object o) {
        return o instanceof StrictTermKey other && term.equalsIncludingLabels(other.term);
    }

    @Override
    public int hashCode() {
        return term.labeledHashCode();
    }
}
