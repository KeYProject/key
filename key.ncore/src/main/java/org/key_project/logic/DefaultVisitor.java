/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

/**
 * This abstract Vistor class declares the interface for a common term visitor.
 */
public abstract class DefaultVisitor<S extends org.key_project.logic.sort.Sort<S>>
        implements Visitor<S> {
    @Override
    public boolean visitSubtree(org.key_project.logic.Term<S> visited) {
        return true;
    }

    @Override
    public void subtreeEntered(org.key_project.logic.Term<S> subtreeRoot) {
    }

    @Override
    public void subtreeLeft(org.key_project.logic.Term<S> subtreeRoot) {
    }
}
