/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;


import de.uka.ilkd.key.ldt.JavaDLTheory;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;


/**
 * The objects of this class represent logical variables, used e.g. for quantification.
 */
public final class LogicVariable extends JAbstractSortedOperator
        implements QuantifiableVariable {

    public LogicVariable(Name name, Sort sort) {
        super(name, sort, true);
        assert sort != JavaDLTheory.FORMULA;
        assert sort != JavaDLTheory.UPDATE;
    }

    @Override
    public String toString() {
        return name() + ":" + sort();
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Logic variable " + name() + " does not have children");
    }
}
