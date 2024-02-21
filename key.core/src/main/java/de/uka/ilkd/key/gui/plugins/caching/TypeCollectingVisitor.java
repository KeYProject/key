package de.uka.ilkd.key.gui.plugins.caching;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;

import java.util.HashMap;
import java.util.Map;

public class TypeCollectingVisitor implements Visitor {
    private final Map<String, String> types = new HashMap<>();
    private final Map<String, String> typesLocVars = new HashMap<>();

    public void visit(Sequent sequent) {
        for (int i = 1; i <= sequent.size(); i++) {
            var f = sequent.getFormulabyNr(i);
            f.formula().execPreOrder(this);
        }
    }

    @Override
    public boolean visitSubtree(Term visited) {
        return true;
    }

    @Override
    public void visit(Term visited) {
        var op = visited.op();
        if (op instanceof Function function) {
            types.put(function.name().toString(), function.argsToString());
        }
        if (op instanceof LocationVariable locationVariable) {
            typesLocVars.put(locationVariable.name().toString(), locationVariable.getKeYJavaType().toString());
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
