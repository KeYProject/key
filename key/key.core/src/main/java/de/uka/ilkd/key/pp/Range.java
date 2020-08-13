// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

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
        if (start != other.start) {
            return false;
        }
        return true;
    }
}