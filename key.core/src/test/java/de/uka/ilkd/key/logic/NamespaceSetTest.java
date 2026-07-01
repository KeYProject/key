/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import org.key_project.logic.MetaSpace;
import org.key_project.logic.Namespace;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotNull;

public class NamespaceSetTest {

    /**
     * {@link NamespaceSet#getParent()} must not leave {@code null} values in the namespace map: a
     * sub-namespace without an enclosing layer has no parent. Copying such a parent set — as
     * {@code Goal.adaptNamespacesNewGoals} does for the additional goals of a splitting rule
     * applied
     * interactively — otherwise fails with a {@link NullPointerException} in
     * {@code Namespace.copy}.
     * Regression test for that crash.
     */
    @Test
    @SuppressWarnings("deprecation")
    public void getParentOfRootNamespacesIsCopyable() {
        // every sub-namespace is a root (no parent), so getParent() sees a null parent for each
        NamespaceSet roots = new NamespaceSet(new Namespace<>(), new Namespace<>(),
            new Namespace<>(), new Namespace<>(), new Namespace<>(), new Namespace<>(),
            new Namespace<>(), new Namespace<>(), new Namespace<>(),
            new MetaSpace(new MetaSpace()));

        NamespaceSet parent = roots.getParent();
        assertNotNull(assertDoesNotThrow(parent::copy,
            "copying a parent namespace set must tolerate a missing (root) parent layer"));
    }
}
