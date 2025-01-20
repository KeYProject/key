/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

/**
 * A class specifying a range of integer numbers e.g. character positions.
 */
public class Range {
    int start = -1;
    int end = -1;

    /**
     * Creates a new range {@code [s,e)}.
     *
     * @param s this range's (included) start position.
     * @param e this range's (excluded) end position.
     */
    public Range(int s, int e) {
        start = s;
        end = e;
    }

    /**
     * Creates a copy of the specified range.
     *
     * @param r the range to copy.
     */
    public Range(Range r) {
        start = r.start;
        end = r.end;
    }

    /**
     *
     * @return this range's (included) start position.
     */
    public int start() {
        return start;
    }

    /**
     *
     * @return this range's (excluded) end position.
     */
    public int end() {
        return end;
    }

    /**
     *
     * @return this range's length.
     */
    public int length() {
        return end - start;
    }

    @Override
    public String toString() {
        return "[ Start = " + start + " ; End = " + end + " ]";
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + end;
        result = prime * result + start;
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        Range other = (Range) obj;
        if (end != other.end) {
            return false;
        }
        return start == other.start;
    }
}
