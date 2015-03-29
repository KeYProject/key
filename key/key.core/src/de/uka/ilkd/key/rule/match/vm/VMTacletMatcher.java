package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;
import java.util.Stack;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.IfMatchResult;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.TacletMatcher;

public class VMTacletMatcher implements TacletMatcher {

    private final IMatchInstruction[] program;

    public VMTacletMatcher(Term pattern) {
        ArrayList<IMatchInstruction<?>> prgList = new ArrayList<>();
        createProgram(pattern, prgList);
        program = new IMatchInstruction[prgList.size()];
        prgList.toArray(program);
    }
    
    private void createProgram(Term pattern, ArrayList<IMatchInstruction<? extends SVSubstitute>> program) {
        final Operator op = pattern.op();

        final JavaProgramElement patternPrg = pattern.javaBlock().program();

        final ImmutableArray<QuantifiableVariable> boundVars = pattern
                .boundVars();
        if (!boundVars.isEmpty()) {
            program.add(Instruction.matchAndBindVariables(boundVars));
        }

        if (!pattern.javaBlock().isEmpty()
                || patternPrg instanceof ContextStatementBlock) {
            program.add(Instruction.matchProgram(patternPrg));
        }

        if (op instanceof SchemaVariable) {
            if (op instanceof ModalOperatorSV) {
                program.add(Instruction
                        .matchModalOperatorSV((ModalOperatorSV) op));
            }
            else if (op instanceof FormulaSV) {
                program.add(Instruction.matchFormulaSV((FormulaSV) op));
            }
            else if (op instanceof TermSV) {
                program.add(Instruction.matchTermSV((TermSV) op));
            }
            else if (op instanceof VariableSV) {
                program.add(Instruction
                        .matchVariableSV((VariableSV) op));
            }
            else if (op instanceof ProgramSV) {
                program.add(Instruction.matchProgramSV((ProgramSV) op));
            }
            else if (op instanceof UpdateSV) {
                program.add(Instruction.matchUpdateSV((UpdateSV) op));
            }
            else if (op instanceof TermLabelSV) {
                program.add(Instruction
                        .matchTermLabelSV((TermLabelSV) op));
            }
            else {
                throw new IllegalArgumentException("Do not know how to match "
                        + op + " of type " + op.getClass());
            }
        }
        else if (op instanceof SortDependingFunction) {
            program.add(Instruction
                    .matchSortDependingFunction((SortDependingFunction) op));
        }
        else {
            program.add(Instruction.matchOp(op));
        }

        for (int i = 0; i < pattern.arity(); i++) {
            createProgram(pattern.sub(i), program);
        }

        if (!boundVars.isEmpty()) {
            program.add(Instruction.unbindVariables(boundVars));
        }
    }

    public MatchConditions match(Term p_toMatch, MatchConditions p_matchCond,
            Services services) {

        MatchConditions mc = p_matchCond;
        int instrPtr = 0;
        
        final TermNavigator navi = new TermNavigator(p_toMatch);
        

        while (mc != null && instrPtr < program.length && navi.hasNext()) {
            mc = program[instrPtr].match(navi, mc, services);
            instrPtr++;
        }

        return mc;
    }

    @Override
    public IfMatchResult matchIf(Iterable<IfFormulaInstantiation> p_toMatch,
            Term p_template, MatchConditions p_matchCond, Services p_services) {
        return null;
    }

    @Override
    public MatchConditions matchIf(Iterable<IfFormulaInstantiation> p_toMatch,
            MatchConditions p_matchCond, Services p_services) {
        return null;
    }

    @Override
    public MatchConditions checkConditions(MatchConditions p_matchconditions,
            Services services) {
        return null;
    }

    @Override
    public MatchConditions checkVariableConditions(SchemaVariable var,
            SVSubstitute instantiationCandidate, MatchConditions matchCond,
            Services services) {
        return null;
    }

    @Override
    public MatchConditions matchFind(Term term, MatchConditions matchCond,
            Services services) {
        return null;
    }

    
    static class TermNavigator {

        /** 
         * top element on stack contains always the pair whose
         * first component is the element to be returned by 
         * {@link #next()} while the second points to the child to 
         * be visited next (or equals the arity of the first component 
         * if no such child exists)
         * For all elements on the stack that are not the top element
         * the second component is less than the arity of the term in the 
         * first component
         */
        private final Stack<MutablePair<Term,Integer>> stack = new Stack<>();
        
        public TermNavigator(Term term) {
            stack.push(new MutablePair<Term,Integer>(term, 0));
        }
        
        
        public boolean hasNext() {
            return !stack.isEmpty();
        }

        public boolean hasNextSibling() {
            return stack.size() > 1;
        }

        
        public Term getCurrentSubterm() {
            return stack.peek().first; 
        }
        
        private /*@ helper @*/ void gotoNextHelper() { 
            if (stack.isEmpty()) {
                return;
            }
            MutablePair<Term, Integer> el = stack.peek();            
            do {
                if (el.second < el.first.arity()) {
                    final int oldPos = el.second;
                    el.second += 1;
                    if (el.second >= el.first.arity()) {
                        // we visited all children of that term
                        // so it can be removed from the stack
                        stack.pop();
                    }
                    el = new MutablePair<Term, Integer>(el.first.sub(oldPos), 0);
                    stack.push(el);
                } else {
                    stack.pop();                    
                }
            } while (!stack.isEmpty() && stack.peek().second != 0);
        }
        
        public void gotoNext() {
            gotoNextHelper();
        }
        
        public void gotoNextSibling() {
            stack.pop();
            gotoNextHelper();            
        }
     
        
        private static class MutablePair<Fst,Snd> {
            private Fst first;
            private Snd second;
            
            public MutablePair(Fst first, Snd second) {
                this.first = first;
                this.second = second;
            }

            @Override
            public String toString() {
                return "MutablePair [first=" + first + ", second=" + second
                        + "]";
            }
        }
        
    }
    
}
