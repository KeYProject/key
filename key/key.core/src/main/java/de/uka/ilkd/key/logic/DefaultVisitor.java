/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.logic;

/**
 * This abstract Vistor class declares the interface for a common term visitor.
 */
public abstract class DefaultVisitor implements Visitor {
    @Override
    public boolean visitSubtree(Term visited) {
        return true;
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {}

    @Override
    public void subtreeLeft(Term subtreeRoot) {}
}
