/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.AssignmentExpression;
import org.key_project.rusty.ast.pat.IdentPattern;
import org.key_project.rusty.ast.pat.Pattern;
import org.key_project.rusty.ast.pat.SchemaVarPattern;
import org.key_project.rusty.ast.ty.SchemaRustType;
import org.key_project.rusty.logic.op.sv.SchemaVariable;
import org.key_project.rusty.rule.inst.SVInstantiations;
import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Walks through a Rust AST in depth-left-fist-order. This walker is used to transform a program
 * according to the given SVInstantiations.
 */
public class ProgramReplaceVisitor extends CreatingASTVisitor {
    private RustyProgramElement result = null;

    private final SVInstantiations svinsts;

    /**
     * create the ProgramReplaceVisitor
     *
     * @param root the ProgramElement where to begin
     * @param services The Services object.
     * @param svi Schema Variable Instantiations
     */
    public ProgramReplaceVisitor(RustyProgramElement root, Services services,
            SVInstantiations svi) {
        super(root, false, services);
        svinsts = svi;
    }

    /** starts the walker */
    @Override
    public void start() {
        assert result == null : "ProgramReplaceVisitor is not designed for multiple walks";
        stack.push(new ExtList());
        walk(root());
        final ExtList astList = stack.pop();
        for (int i = 0, sz = astList.size(); result == null && i < sz; i++) {
            final Object element = astList.get(i);
            if (element instanceof RustyProgramElement pe) {
                result = pe;
            }
        }
    }

    /**
     * @return The result.
     */
    public RustyProgramElement result() {
        return result;
    }

    /**
     * the implemented default action is called if a program element is, and if it has children all
     * its children too are left unchanged
     */
    @Override
    protected void doDefaultAction(RustyProgramElement x) {
        addChild(x);
    }

    @Override
    public void performActionOnAssignmentExpression(AssignmentExpression x) {
        ExtList changeList = stack.peek();
        if (!changeList.isEmpty() && changeList.getFirst() == CHANGED) {
            changeList.removeFirst();
            Pattern pat = changeList.removeFirstOccurrence(Pattern.class);
            if (pat != null) {
                if (pat instanceof IdentPattern ip) {
                    var pv = ip.programVariable();
                    stack.pop();
                    var el = new ExtList();
                    assert pv != null;
                    el.add(pv);
                    el.addAll(changeList);
                    stack.push(el);
                    changed();
                }
            }
        }
        super.performActionOnAssignmentExpression(x);
    }

    @Override
    public void performActionOnSchemaVarPattern(SchemaVarPattern x) {

    }

    @Override
    public void performActionOnSchemaRustType(SchemaRustType x) {
        var sv = x.type().sv();
        final Object inst = svinsts.getInstantiation(sv);
        if (inst instanceof RustyProgramElement pe) {
            addChild(pe);
        } else {
            throw new IllegalStateException(
                "programreplacevisitor: Instantiation missing " + "for schema variable " + sv);
        }
        changed();
    }

    @Override
    public void performActionOnSchemaVariable(SchemaVariable sv) {
        final Object inst = svinsts.getInstantiation(sv);
        if (inst instanceof RustyProgramElement pe) {
            addChild(pe);
        } else if (inst instanceof ImmutableArray/* <ProgramElement> */) {
            @SuppressWarnings("unchecked")
            final var instArray = (ImmutableArray<RustyProgramElement>) inst;
            // the assertion ensures the intended instanceof check from above
            addChildren(instArray);
        } /*
           * TODO: else if (inst instanceof Term t && t.op() instanceof ProgramInLogic) {
           * addChild(services.getTypeConverter().convertToProgramElement((Term) inst));
           * }
           */ else {
            throw new IllegalStateException(
                "programreplacevisitor: Instantiation missing " + "for schema variable " + sv);
        }
        changed();
    }
}
