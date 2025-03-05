/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Top level implementation of a Java {@link NonTerminalProgramElement}. taken from COMPOST and
 * changed to achieve an immutable structure
 */
public abstract class JavaNonTerminalProgramElement extends JavaProgramElement
        implements NonTerminalProgramElement {

    protected JavaNonTerminalProgramElement() {
    }


    /**
     * Java program element.
     *
     * @param list as ExtList with children of the node
     */
    protected JavaNonTerminalProgramElement(ExtList list) {
        super(list);
    }


    protected JavaNonTerminalProgramElement(PositionInfo pos) {
        super(pos);
    }


    protected JavaNonTerminalProgramElement(ExtList children, PositionInfo pos) {
        super(children, pos);
    }


    /**
     * returns the index of element el in array arr
     *
     * @param arr the array where the element is looked for
     * @param el the element to look for
     * @return the index of the element (-1 if not found)
     */
    protected int getArrayPos(ImmutableArray<ProgramElement> arr, ProgramElement el) {
        for (int i = 0, sz = arr.size(); i < sz; i++) {
            if (arr.get(i) == el) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o == null || o.getClass() != this.getClass()) {
            return false;
        }

        final JavaNonTerminalProgramElement jnte = (JavaNonTerminalProgramElement) o;
        if (jnte.getChildCount() != getChildCount()) {
            return false;
        }

        for (int i = 0, cc = getChildCount(); i < cc; i++) {
            if (!getChildAt(i).equals(jnte.getChildAt(i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected int computeHashCode() {
        int localHash = 17 * super.computeHashCode();
        for (int i = 0, sz = getChildCount(); i < sz; i++) {
            final ProgramElement pe = getChildAt(i);
            localHash = 17 * localHash + (pe == null ? 0 : pe.hashCode());
        }
        return localHash;
    }

    @Override
    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();

        if (src == null) {
            return null;
        }

        if (src.getClass() != this.getClass()) {
            return null;
        }

        final NonTerminalProgramElement ntSrc = (NonTerminalProgramElement) src;
        final SourceData newSource = new SourceData(ntSrc, 0, source.getServices());

        matchCond = matchChildren(newSource, matchCond, 0);

        if (matchCond == null) {
            return null;
        }

        source.next();
        return matchCond;
    }


    /**
     * used by @link matchChildren to decide if a found match is valid or if there are remaining
     * source elements that have not been matched (in which case the match failed)
     */
    protected boolean compatibleBlockSize(int pos, int max) {
        return pos >= max;
    }


    /**
     * matches successively all children of this current node. Thereby the <tt>offset</tt>-th child
     * is matched against <code>source.getSource()</code>. The call <tt>source.next</tt> has to be
     * done in the @link ProgramElement#match method of the currently matched child in case of a
     * successful match. This is <em>not</em> done here (rationale: schemavariables matching on
     * lists can be implemented easy).
     *
     *
     * @param source the SourceData with the children to be matched
     * @param matchCond the MatchConditions found so far
     * @param offset the int denoting the index of the child to start with
     * @return the resulting match conditions or <tt>null</tt> if matching failed
     */
    protected MatchConditions matchChildren(SourceData source, MatchConditions matchCond,
            int offset) {

        for (int i = offset, sz = getChildCount(); i < sz; i++) {
            matchCond = getChildAt(i).match(source, matchCond);
            if (matchCond == null) {
                return null;
            }
        }

        final NonTerminalProgramElement ntSrc = (NonTerminalProgramElement) source.getElement();

        if (!compatibleBlockSize(source.getChildPos(), ntSrc.getChildCount())) {
            return null;
        }

        return matchCond;
    }
}
