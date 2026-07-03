/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Function;

/**
 * Assigns stable, order-independent numbers {@code 0, 1, 2, ...} to the members of a group, so a
 * number that ends up in a persisted name -- e.g. a class-axiom or partial-invariant taclet name --
 * depends only on <em>which contents are present in the group</em>, never on the order the members
 * were parsed, iterated or created in. The numbering is therefore reproducible across runs, reloads
 * and prune-and-redo, which an incrementing counter is not.
 *
 * <p>
 * Each member is numbered by the rank of its <em>content key</em> in the sorted set of the group's
 * content keys. Distinct content keys receive distinct, gap-free numbers; members that share a
 * content key share a number (they are indistinguishable by content, i.e. duplicates), which is why
 * this is collision-free by construction rather than a hash that could clash for different
 * contents.
 *
 * <p>
 * Intended to replace order-dependent counters that leak into taclet names. The content key must be
 * a deterministic function of the member's content (a canonical string form).
 *
 * @param <T> the member type
 */
public final class ContentOrderNumbering<T> {

    private final Function<? super T, String> contentKey;
    private final Map<String, Integer> numberByKey;

    /**
     * Builds the numbering for {@code group}.
     *
     * @param group the members to number (order irrelevant)
     * @param contentKey a deterministic, content-derived key for a member
     */
    public ContentOrderNumbering(Iterable<? extends T> group,
            Function<? super T, String> contentKey) {
        this.contentKey = contentKey;
        final SortedSet<String> keys = new TreeSet<>();
        for (T member : group) {
            keys.add(contentKey.apply(member));
        }
        final Map<String, Integer> byKey = new HashMap<>();
        int number = 0;
        for (String key : keys) {
            byKey.put(key, number++);
        }
        this.numberByKey = byKey;
    }

    /**
     * @param member a member of the group this numbering was built for (matched by content key)
     * @return its stable number
     * @throws IllegalArgumentException if no member with {@code member}'s content key was in the
     *         group
     */
    public int numberOf(T member) {
        final Integer number = numberByKey.get(contentKey.apply(member));
        if (number == null) {
            throw new IllegalArgumentException(
                "member is not part of the numbering group: " + member);
        }
        return number;
    }
}
