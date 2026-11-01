/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.pp;


import java.util.Objects;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This is a position table for program modality formulae. In addition to the usual tables, it can
 * store a range of character positions for the first statement in the Java block.
 */

@NullMarked
public class ModalityPositionTable extends PositionTable {

    public ModalityPositionTable(int rows) {
        super(rows);
    }

    private @Nullable Range firstStatementRange = null;


    public void setFirstStatementRange(Range r) {
        firstStatementRange = r;
    }


    public Range getFirstStatementRange() {
        // The range exists only after the layouter saw MARK_START/END_FIRST_STMT for a modality;
        // its absence used to fail inside the Range copy constructor, so the copy source is
        // asserted non-null here to keep that failure shape.
        return new Range(Objects.requireNonNull(firstStatementRange,
            "no first statement range recorded for this modality"));
    }
}
