/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.util.LinkedList;
import java.util.List;
import java.util.Stack;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.statement.Break;
import de.uka.ilkd.key.java.ast.statement.Continue;
import de.uka.ilkd.key.java.ast.statement.LabelJumpStatement;
import de.uka.ilkd.key.java.ast.statement.LabeledStatement;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.ast.statement.Return;
import de.uka.ilkd.key.java.ast.statement.Switch;

public class OuterBreakContinueAndReturnCollector extends JavaASTVisitor {

    private final List<Break> breaks;
    private final List<Continue> continues;
    private final List<Return> returns;

    private int loopAndSwitchCascadeDepth;
    private final Stack<Label> labels;
    private final Stack<MethodFrame> frames;

    public OuterBreakContinueAndReturnCollector(final ProgramElement root,
            final List<Label> alwaysInnerLabels, final Services services) {
        super(root, services);
        breaks = new LinkedList<>();
        continues = new LinkedList<>();
        returns = new LinkedList<>();
        labels = new Stack<>();
        labels.addAll(alwaysInnerLabels);
        frames = new Stack<>();
    }

    public List<Break> getBreaks() {
        return breaks;
    }

    public List<Continue> getContinues() {
        return continues;
    }

    public List<Return> getReturns() {
        return returns;
    }

    public boolean hasReturns() {
        return !returns.isEmpty();
    }

    public void collect() {
        start();
    }

    @Override
    public void start() {
        loopAndSwitchCascadeDepth = 0;
        super.start();
    }

    @Override
    protected void walk(final ProgramElement node) {
        if (node instanceof LoopStatement || node instanceof Switch) {
            loopAndSwitchCascadeDepth++;
        }
        if (node instanceof LabeledStatement) {
            labels.push(((LabeledStatement) node).getLabel());
        }
        if (node instanceof MethodFrame) {
            frames.push((MethodFrame) node);
        }
        super.walk(node);
        if (node instanceof MethodFrame) {
            frames.pop();
        }
        if (node instanceof LabeledStatement) {
            labels.pop();
        }
        if (node instanceof LoopStatement || node instanceof Switch) {
            loopAndSwitchCascadeDepth--;
        }
    }

    @Override
    protected void doAction(final ProgramElement node) {
        if (node instanceof Break || node instanceof Continue || node instanceof Return) {
            node.visit(this);
        }
    }

    @Override
    protected void doDefaultAction(final SourceElement x) {
        // do nothing
    }

    @Override
    public void performActionOnBreak(final Break x) {
        if (isJumpToOuterLabel(x)) {
            breaks.add(x);
        }
    }

    @Override
    public void performActionOnContinue(final Continue x) {
        if (isJumpToOuterLabel(x)) {
            continues.add(x);
        }
    }

    private boolean isJumpToOuterLabel(final LabelJumpStatement x) {
        return loopAndSwitchCascadeDepth == 0 && x.getProgramElementName() == null
                || x.getLabel() != null && labels.search(x.getLabel()) == -1;
    }

    @Override
    public void performActionOnReturn(final Return x) {
        if (frames.empty()) {
            returns.add(x);
        }
    }

}
