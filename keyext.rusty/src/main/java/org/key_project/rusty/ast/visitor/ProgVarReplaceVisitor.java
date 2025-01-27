/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import java.util.HashMap;
import java.util.Map;

import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.InfiniteLoopExpression;
import org.key_project.rusty.logic.TermBuilder;
import org.key_project.rusty.logic.op.ElementaryUpdate;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.speclang.LoopSpecImpl;
import org.key_project.rusty.speclang.LoopSpecification;
import org.key_project.rusty.util.MiscTools;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Walks through a java AST in depth-left-first-order. This visitor replaces a number of program
 * variables by others or new ones.
 */
public class ProgVarReplaceVisitor extends CreatingASTVisitor {
    protected boolean replaceallbynew = true;

    /**
     * stores the program variables to be replaced as keys and the new program variables as values
     */
    protected final Map<ProgramVariable, ProgramVariable> replaceMap;

    private RustyProgramElement result = null;

    /**
     * creates a visitor that replaces the program variables in the given statement by new ones with
     * the same name
     *
     * @param st the statement where the prog vars are replaced
     * @param map the HashMap with the replacements
     * @param services the services instance
     */
    public ProgVarReplaceVisitor(RustyProgramElement st, Map<ProgramVariable, ProgramVariable> map,
            boolean replaceallbynew,
            Services services) {
        super(st, true, services);
        this.replaceallbynew = replaceallbynew;
        this.replaceMap = map;
        assert services != null;
    }

    /**
     * the action that is performed just before leaving the node the last time
     *
     * @param node the node described above
     */
    @Override
    protected void doAction(RustyProgramElement node) {
        node.visit(this);
    }

    /** starts the walker */
    @Override
    public void start() {
        stack.push(new ExtList());
        walk(root());
        ExtList el = stack.peek();
        int i = 0;
        while (!(el.get(i) instanceof RustyProgramElement)) {
            i++;
        }
        result = (RustyProgramElement) stack.peek().get(i);
    }

    public RustyProgramElement result() {
        return result;
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        RustyProgramElement newPV = replaceMap.get(x);
        if (newPV != null) {
            addChild(newPV);
            changed();
        } else {
            doDefaultAction(x);
        }
    }

    @Override
    protected void performActionOnLoopInvariant(InfiniteLoopExpression old,
            InfiniteLoopExpression newLoop) {
        final TermBuilder tb = services.getTermBuilder();
        LoopSpecification inv = services.getSpecificationRepository().getLoopSpec(old);
        if (inv == null)
            return;

        var atPres = inv.getInternalAtPres();

        var newInv = replaceVariablesInTerm(inv.getInvariant(atPres, services));

        var newVar = replaceVariablesInTerm(inv.getVariant(atPres, services));

        Map<ProgramVariable, Term> saveCopy = new HashMap<>(atPres);
        for (var e : saveCopy.entrySet()) {
            var pv = e.getKey();
            final var t = e.getValue();
            if (t == null)
                continue;
            if (replaceMap.containsKey(pv)) {
                atPres.remove(pv);
                pv = replaceMap.get(pv);
            }
            atPres.put(pv, replaceVariablesInTerm(t));
        }

        var newLocalIns = tb.var(MiscTools.getLocalIns(newLoop, services));
        var newLocalOuts = tb.var(MiscTools.getLocalOuts(newLoop, services));
        var newSpec = new LoopSpecImpl(newLoop, newInv, newVar, newLocalIns, newLocalOuts, atPres);
        services.getSpecificationRepository().addLoopSpec(newSpec);
    }

    private Term replaceVariablesInTerm(Term t) {
        if (t == null)
            return null;
        if (t.op() instanceof ProgramVariable pv) {
            if (replaceMap.containsKey(pv)) {
                ProgramVariable replacement = replaceMap.get(pv);
                return services.getTermFactory().createTerm(replacement);
            } else {
                return t;
            }
        } else {
            boolean changed = false;
            Term[] subTerms = new Term[t.arity()];
            for (int i = 0, n = t.arity(); i < n; i++) {
                subTerms[i] = replaceVariablesInTerm(t.sub(i));
                changed = changed || subTerms[i] != t.sub(i);
            }
            Operator op = t.op();
            if (op instanceof ElementaryUpdate eu) {
                if (replaceMap.containsKey(eu.lhs())) {
                    ProgramVariable replacement = replaceMap.get(eu.lhs());
                    op = ElementaryUpdate.getInstance(replacement);
                    changed = changed || eu != op;
                }
            }
            return changed ? services.getTermFactory().createTerm(op, subTerms,
                (ImmutableArray<QuantifiableVariable>) t.boundVars()) : t;
        }
    }
}
