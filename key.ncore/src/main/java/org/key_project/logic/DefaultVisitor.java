/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

/**
 * This abstract Vistor class declares the interface for a common term visitor.
 */
public abstract class DefaultVisitor<T extends Term>
        implements Visitor<T> {
    @Override
    public boolean visitSubtree(T visited) {
        return true;
    }

    @Override
    public void subtreeEntered(T subtreeRoot) {
    }

    @Override
    public void subtreeLeft(T subtreeRoot) {
    }
}
