/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

/**
 * The abstract superclass of caches for taclet app indexes that are separated by different prefixes
 * of bound variables. This class simply stores a <code>IList<QuantifiableVariable></code> and
 * offers a couple of access functions to this list.
 */
abstract class PrefixTermTacletAppIndexCache implements ITermTacletAppIndexCache {

    private final ImmutableList<QuantifiableVariable> prefix;

    protected PrefixTermTacletAppIndexCache(ImmutableList<QuantifiableVariable> prefix) {
        this.prefix = prefix;
    }

    protected ImmutableList<QuantifiableVariable> getPrefix() {
        return prefix;
    }

    protected ImmutableList<QuantifiableVariable> getExtendedPrefix(
            ImmutableArray<QuantifiableVariable> extension) {
        ImmutableList<QuantifiableVariable> res = prefix;
        for (int i = 0; i != extension.size(); ++i) {
            res = res.prepend(extension.get(i));
        }
        return res;
    }

    protected ImmutableList<QuantifiableVariable> getExtendedPrefix(Term t, int subtermIndex) {
        return getExtendedPrefix(t.varsBoundHere(subtermIndex));
    }

}
