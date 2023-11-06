/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

public class ProxySort extends SortImpl {

    public ProxySort(Name name, ImmutableSet<Sort> ext, String documentation, String origin) {
        super(name, ext, false, documentation, origin);
    }

    public ProxySort(Name name) {
        this(name, DefaultImmutableSet.nil(), "", "");
    }
}
