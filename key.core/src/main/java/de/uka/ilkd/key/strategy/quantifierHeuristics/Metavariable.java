/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.AbstractSortedOperator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.sort.Sort;

@Deprecated
public final class Metavariable extends AbstractSortedOperator
        implements ParsableVariable, Comparable<Metavariable> {

    // Used to define an alternative order of all existing
    // metavariables
    private static int maxSerial = 0;
    private int serial;

    private final boolean isTemporaryVariable;

    private synchronized void setSerial() {
        serial = maxSerial++;
    }

    private Metavariable(Name name, Sort sort, boolean isTemporaryVariable) {
        super(name, sort, true);
        if (sort == Sort.FORMULA) {
            throw new RuntimeException("Attempt to create metavariable of type formula");
        }
        this.isTemporaryVariable = isTemporaryVariable;
        setSerial();
        // assert false : "metavariables are disabled";
    }

    public Metavariable(Name name, Sort sort) {
        this(name, sort, false);
    }

    @Override
    public String toString() {
        return name() + ":" + sort();
    }


    @Override
    public int compareTo(Metavariable p_mr) {
        if (p_mr == this) {
            return 0;
        }
        if (p_mr == null) {
            throw new NullPointerException();
        }

        // temporary variables are the greatest ones
        if (isTemporaryVariable()) {
            if (!p_mr.isTemporaryVariable()) {
                return 1;
            }
        } else {
            if (p_mr.isTemporaryVariable()) {
                return -1;
            }
        }

        int t = name().toString().compareTo(p_mr.name().toString());
        if (t == 0) {
            return serial < p_mr.serial ? -1 : 1;
        }
        return t;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof Metavariable)) {
            return false;
        }
        return compareTo((Metavariable) o) == 0;
    }

    /**
     * @return Returns the isTemporaryVariable.
     */
    public boolean isTemporaryVariable() {
        return isTemporaryVariable;
    }
}
