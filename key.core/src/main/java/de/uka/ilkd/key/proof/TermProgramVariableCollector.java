/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.logic.DefaultVisitor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.op.Function;

public class TermProgramVariableCollector implements DefaultVisitor {

    private final HashSet<LocationVariable> result = new LinkedHashSet<>();
    private final Services services;
    private final DependenciesLDT dependenciesLDT;
    private boolean containsNonRigidFunctionSymbols = false;
    private boolean containsAtMostDepPredAsNonRigid = true;


    public TermProgramVariableCollector(Services services) {
        this.services = services;
        this.dependenciesLDT = services.getTypeConverter().getDependenciesLDT();
    }

    /**
     * is called by the execPostOrder-method of a term
     *
     * @param visited the Term to checked if it is a program variable and if true the variable is
     *        added
     *        to the list of found variables
     */
    public void visit(Term visited) {
        if (visited.op() instanceof LocationVariable variable) {
            result.add(variable);
        } else if (visited.op() instanceof Function && !visited.op().isRigid()) { // term contains
                                                                                  // non-rigid
                                                                                  // symbols that
                                                                                  // are not program
                                                                                  // variables
            containsNonRigidFunctionSymbols = true;
            boolean dependencePredicate = dependenciesLDT.isDependencePredicate(visited.op());
            containsAtMostDepPredAsNonRigid &= dependencePredicate;
        }

        if (!visited.javaBlock().isEmpty()) {
            ProgramVariableCollector pvc =
                new ProgramVariableCollector(visited.javaBlock().program(), services);
            pvc.start();
            result.addAll(pvc.result());
        }
    }

    public HashSet<LocationVariable> result() {
        return result;
    }

    public boolean containsAtMostDepPredAsNonRigid() {
        return containsAtMostDepPredAsNonRigid;
    }

    public boolean containsNonRigidNonProgramVariableSymbol() {
        return containsNonRigidFunctionSymbols;
    }
}
