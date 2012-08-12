package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.*;

import java.util.*;

public class OuterBreakContinueAndReturnCollector extends JavaASTVisitor {

    //private final SVInstantiations instantiations;

    private final List<Break> breaks;
    private final List<Continue> continues;
    private final List<Return> returns;

    private int loopAndSwitchCascadeDepth;
    private final Stack<Label> labels;
    private final Stack<MethodFrame> frames;

    public OuterBreakContinueAndReturnCollector(final ProgramElement root/*, final SVInstantiations instantiations*/, final Services services) {
        super(root, services);
        //this.instantiations = (instantiations == null ? SVInstantiations.EMPTY_SVINSTANTIATIONS : instantiations);
        breaks = new LinkedList<Break>();
        continues = new LinkedList<Continue>();
        returns = new LinkedList<Return>();
        labels = new Stack<Label>();
        frames = new Stack<MethodFrame>();
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

    public void collect()
    {
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
        if (node instanceof Break || node instanceof Continue || node instanceof Return /*|| node instanceof SchemaVariable*/) {
            node.visit(this);
        }
    }

    @Override
    protected void doDefaultAction(final SourceElement x) {
        // do nothing
    }

    /*@Override
    public void performActionOnSchemaVariable(final SchemaVariable sv) {
        final Object buffer = instantiations.getInstantiation(sv);
        if (buffer == null) {
            // we cannont decide whether there are unlabeled breaks that is why both labels are needed
            needInnerLabel = true;
            needOuterLabel = true;
        } else {
            if (buffer instanceof ProgramElement) {
                walk((ProgramElement) buffer);
            } else {
                final ImmutableArray<Statement> aope = (ImmutableArray<Statement>) buffer;
                for (int iterate = 0; iterate < aope.size(); iterate++) {
                    ProgramElement pe = aope.get(iterate);
                    if (pe != null) {
                        walk(pe);
                    }
                }
            }
        }
    }*/

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

    protected boolean isJumpToOuterLabel(final LabelJumpStatement x) {
        return loopAndSwitchCascadeDepth == 0 && x.getProgramElementName() == null
                || x.getLabel() != null && labels.search(x.getLabel()) == -1
                /*|| labels.contains(x.getProgramElementName())*/;
    }

    @Override
    public void performActionOnReturn(final Return x) {
        if (frames.empty()) {
            returns.add(x);
        }
        /*else {
            frames.pop();
        }*/
    }

}