/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.sort.Sort;

import de.uka.ilkd.key.logic.DefaultVisitor;

public class TermProgramVariableCollector extends DefaultVisitor {

    private final HashSet<LocationVariable> result = new LinkedHashSet<>();
    private final Services services;


    public TermProgramVariableCollector(Services services) {
        this.services = services;
    }

    /**
     * is called by the execPostOrder-method of a term
     *
     * @param term the Term to checked if it is a program variable and if true the variable is added
     *        to
     *        the list of found variables
     */
    public void visit(Term term) {
        var t = (Term) term;
        if (t.op() instanceof LocationVariable) {
            result.add((LocationVariable) t.op());
        }

        if (!t.javaBlock().isEmpty()) {
            ProgramVariableCollector pvc =
                new ProgramVariableCollector(t.javaBlock().program(), services);
            pvc.start();
            result.addAll(pvc.result());
        }
    }

    public HashSet<LocationVariable> result() {
        return result;
    }
}
