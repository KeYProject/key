// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.*;

import java.util.*;

public class OuterBreakContinueAndReturnCollector extends JavaASTVisitor {

    private final List<Break> breaks;
    private final List<Continue> continues;
    private final List<Return> returns;

    private int loopAndSwitchCascadeDepth;
    private final Stack<Label> labels;
    private final Stack<MethodFrame> frames;

    public OuterBreakContinueAndReturnCollector(final ProgramElement root, final List<Label> alwaysInnerLabels, final Services services)
    {
        super(root, services);
        breaks = new LinkedList<Break>();
        continues = new LinkedList<Continue>();
        returns = new LinkedList<Return>();
        labels = new Stack<Label>();
        labels.addAll(alwaysInnerLabels);
        frames = new Stack<MethodFrame>();
    }

    public List<Break> getBreaks()
    {
        return breaks;
    }

    public List<Continue> getContinues()
    {
        return continues;
    }

    public List<Return> getReturns()
    {
        return returns;
    }

    public boolean hasReturns()
    {
        return !returns.isEmpty();
    }

    public void collect()
    {
        start();
    }

    @Override
    public void start()
    {
        loopAndSwitchCascadeDepth = 0;
        super.start();
    }

    @Override
    protected void walk(final ProgramElement node)
    {
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
    protected void doAction(final ProgramElement node)
    {
        if (node instanceof Break || node instanceof Continue || node instanceof Return) {
            node.visit(this);
        }
    }

    @Override
    protected void doDefaultAction(final SourceElement x)
    {
        // do nothing
    }

    @Override
    public void performActionOnBreak(final Break x)
    {
        if (isJumpToOuterLabel(x)) {
            breaks.add(x);
        }
    }

    @Override
    public void performActionOnContinue(final Continue x)
    {
        if (isJumpToOuterLabel(x)) {
            continues.add(x);
        }
    }

    private boolean isJumpToOuterLabel(final LabelJumpStatement x)
    {
        return loopAndSwitchCascadeDepth == 0 && x.getProgramElementName() == null
                || x.getLabel() != null && labels.search(x.getLabel()) == -1;
    }

    @Override
    public void performActionOnReturn(final Return x)
    {
        if (frames.empty()) {
            returns.add(x);
        }
    }

}