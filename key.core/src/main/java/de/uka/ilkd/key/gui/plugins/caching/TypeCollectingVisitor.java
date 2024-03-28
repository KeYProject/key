/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;

import org.key_project.logic.Visitor;
import org.key_project.logic.op.Function;

public class TypeCollectingVisitor implements Visitor<Term> {
    private final Map<String, String> types = new HashMap<>();
    private final Map<String, String> typesLocVars = new HashMap<>();

    public void visit(Sequent sequent) {
        for (int i = 1; i <= sequent.size(); i++) {
            var f = sequent.getFormulabyNr(i);
            f.formula().execPreOrder(this);
        }
    }

    @Override
    public void visit(Term visited) {
        var op = visited.op();
        if (op instanceof Function function) {
            types.put(function.name().toString(), function.argsToString());
        }
        if (op instanceof LocationVariable locationVariable) {
            typesLocVars.put(locationVariable.name().toString(),
                locationVariable.getKeYJavaType().toString());
        }
    }

    @Override
    public void subtreeEntered(Term subtreeRoot) {

    }

    @Override
    public void subtreeLeft(Term subtreeRoot) {

    }

    public Map<String, String> getTypes() {
        return types;
    }

    public Map<String, String> getTypesLocVars() {
        return typesLocVars;
    }
}
