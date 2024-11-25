/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op.sv;

import org.key_project.logic.Name;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.rusty.logic.RustyDLTheory;
import org.key_project.rusty.pp.Layouter;

import org.jspecify.annotations.NonNull;

public class UpdateSV extends OperatorSV implements TerminalSyntaxElement {
    UpdateSV(Name name) {
        super(name, RustyDLTheory.UPDATE, false, true);
    }


    @Override
    public @NonNull String toString() {
        return toString("update");
    }

    @Override
    public void layout(Layouter<?> l) {
        l.print("\\schemaVar \\update ").print(name().toString());
    }
}
