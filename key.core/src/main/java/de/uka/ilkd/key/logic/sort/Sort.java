/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.HasOrigin;

import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;


public interface Sort extends org.key_project.logic.sort.Sort<Sort>, HasOrigin {
    /**
     * Formulas are represented as "terms" of this sort.
     */
    Sort FORMULA = new SortImpl(new Name("Formula"), null, "", "");

    /**
     * Updates are represented as "terms" of this sort.
     */
    Sort UPDATE = new SortImpl(new Name("Update"), null, "", "");

    /**
     * Term labels are represented as "terms" of this sort.
     */
    Sort TERMLABEL = new SortImpl(new Name("TermLabel"), null, "", "");

    /**
     * Any is a supersort of all sorts.
     */
    Sort ANY = new SortImpl(new Name("any"), null, "", "");

    /**
     * @param services services.
     * @return the direct supersorts of this sort.
     */
    ImmutableSet<Sort> extendsSorts(Services services);

}
