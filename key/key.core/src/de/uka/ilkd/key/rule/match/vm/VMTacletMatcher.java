package de.uka.ilkd.key.rule.match.vm;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Stack;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.IfFormulaInstantiation;
import de.uka.ilkd.key.rule.IfMatchResult;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NotFreeIn;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletMatcher;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;
import de.uka.ilkd.key.util.Pair;

public class VMTacletMatcher implements TacletMatcher {

    public static VMTacletMatcher createVMTacletMatcher(Taclet taclet) {
        return new VMTacletMatcher(taclet);
    }


    private final IMatchInstruction[] findMatchProgram;
    private final HashMap<Term, IMatchInstruction[]> assumesMatchPrograms = new HashMap<>();
    

    private final ImmutableList<VariableCondition> varconditions;
    private final Sequent assumesSequent;
    private final ImmutableSet<QuantifiableVariable> boundVars;
    private final ImmutableList<NotFreeIn> varsNotFreeIn;
    
    private final boolean ignoreTopLevelUpdates;
    private final Term findExp;
   
    /**
     * @param taclet the Taclet matched by this matcher
     */
    private VMTacletMatcher(Taclet taclet) {
        varconditions = taclet.getVariableConditions();
        assumesSequent = taclet.ifSequent();
        boundVars = taclet.getBoundVariables();
        varsNotFreeIn = taclet.varsNotFreeIn();

        if (taclet instanceof FindTaclet) {
            ignoreTopLevelUpdates = ((FindTaclet) taclet).ignoreTopLevelUpdates();
            findExp = ((FindTaclet) taclet).find();
        } else {
            ignoreTopLevelUpdates = false;
            findExp = null;
        }     

        ArrayList<IMatchInstruction> prgList = new ArrayList<>();
        if (findExp != null) { 
            createProgram(findExp, prgList);
        }
        findMatchProgram = new IMatchInstruction[prgList.size()];
        prgList.toArray(findMatchProgram);
        
        for (SequentFormula sf : assumesSequent) {
            ArrayList<IMatchInstruction> assumeFmlProgramList = new ArrayList<>();
            createProgram(sf.formula(), assumeFmlProgramList);
            IMatchInstruction[] assumeFmlMatchProgram = new IMatchInstruction[assumeFmlProgramList.size()];
            assumeFmlProgramList.toArray(assumeFmlMatchProgram);
            assumesMatchPrograms.put(sf.formula(), assumeFmlMatchProgram);
        }
    }
    
    
/*    public VMTacletMatcher(Term pattern) {
        ArrayList<IMatchInstruction<?>> prgList = new ArrayList<>();
        createProgram(pattern, prgList);
        program = new IMatchInstruction[prgList.size()];
        prgList.toArray(program);
    } */
    
    private void createProgram(Term pattern, ArrayList<IMatchInstruction> program) {
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

        if (pattern.hasLabels()) {
            program.add(Instruction.matchTermLabelSV(pattern.getLabels()));
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

    public MatchConditions match(Term p_toMatch, 
            IMatchInstruction[] p_program, 
            MatchConditions p_matchCond,
            Services services) {

        MatchConditions mc = p_matchCond;
        int instrPtr = 0;
        
        final TermNavigator navi = new TermNavigator(p_toMatch);
        

        while (mc != null && instrPtr < p_program.length && navi.hasNext()) {
            mc = p_program[instrPtr].match(navi, mc, services);
            instrPtr++;
        }

        return mc;
    }
    /** (non-Javadoc)
     * @see de.uka.ilkd.key.rule.TacletMatcher#matchIf(java.util.Iterator, de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    @Override
    public final IfMatchResult matchIf (   Iterable<IfFormulaInstantiation> p_toMatch,
            Term                             p_template,
            MatchConditions                  p_matchCond,
            Services                         p_services ) {
        IMatchInstruction[] prg = getProgramFor(p_template);

        
        ImmutableList<IfFormulaInstantiation> resFormulas = ImmutableSLList.<IfFormulaInstantiation>nil();
        ImmutableList<MatchConditions> resMC = ImmutableSLList.<MatchConditions>nil();

        final boolean updateContextPresent = 
                !p_matchCond.getInstantiations().getUpdateContext().isEmpty();
        ImmutableList<UpdateLabelPair> context = 
                ImmutableSLList.<SVInstantiations.UpdateLabelPair>nil();
        
        if (updateContextPresent) { 
            context = p_matchCond.getInstantiations().getUpdateContext();   
        }
        
        outer: for (IfFormulaInstantiation cf: p_toMatch) {
            Term formula = cf.getConstrainedFormula().formula();
            ImmutableList<UpdateLabelPair> curContext = context;
            if (updateContextPresent) {                 
                for (int i = 0; i<context.size(); i++) {
                    if (formula.op() instanceof UpdateApplication) {
                        Term update = UpdateApplication.getUpdate(formula);
                        formula = UpdateApplication.getTarget(formula); 
                        ImmutableArray<TermLabel> updateLabel = update.getLabels();
                        UpdateLabelPair ulp = curContext.head();
                        curContext = curContext.tail();
                        if (!ulp.getUpdate().equalsModRenaming(update) ||
                                !ulp.getUpdateApplicationlabels().equals(updateLabel)) {
                            continue outer;
                        }
                    } else {
                        continue outer;
                    }
                }
            }
            
            final MatchConditions newMC = 
            checkConditions(match(formula, prg, p_matchCond, p_services), p_services);
            if (newMC != null) {
                resFormulas = resFormulas.prepend(cf);
                resMC       = resMC.prepend(newMC);
            }
        }

        return new IfMatchResult ( resFormulas, resMC );
    }


    private IMatchInstruction[] getProgramFor(Term p_template) {
        return assumesMatchPrograms.get(p_template);
    }


    /**
     * @see de.uka.ilkd.key.rule.TacletMatcher#matchIf(java.lang.Iterable, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    @Override
    public final MatchConditions matchIf ( Iterable<IfFormulaInstantiation> p_toMatch,
            MatchConditions                  p_matchCond,
            Services                         p_services ) {

        final Iterator<SequentFormula>     itIfSequent   = assumesSequent .iterator ();

        ImmutableList<MatchConditions>            newMC;   

        for (final IfFormulaInstantiation candidateInst: p_toMatch) {
            while ( itIfSequent.hasNext () ) {
                newMC = matchIf ( ImmutableSLList.<IfFormulaInstantiation>nil()
                        .prepend ( candidateInst ),
                        itIfSequent.next ().formula (),
                        p_matchCond,
                        p_services ).getMatchConditions ();

                if ( newMC.isEmpty() )
                    return null;

                p_matchCond = newMC.head ();
            }
        }

        return p_matchCond;
    }

    /**
     * {@inheritDoc}
     */
    public final MatchConditions checkConditions(MatchConditions cond, Services services) {
        MatchConditions result = cond;
        if (result != null) {
            final Iterator<SchemaVariable> svIterator = 
                    cond.getInstantiations().svIterator();

            if (!svIterator.hasNext()) {
                return checkVariableConditions(null, null, cond, services);//XXX
            }

            while (result != null && svIterator.hasNext()) {
                final SchemaVariable sv = svIterator.next();
                final Object o = result.getInstantiations().getInstantiation(sv);
                if (o instanceof SVSubstitute) {
                    result = checkVariableConditions(sv, (SVSubstitute)o , result, services);
                }
            }
        }

        return result;
    }

    /**
     * looks if a variable is declared as not free in
     * @param var the SchemaVariable to look for
     * @return true iff declared not free
     */
    private boolean varDeclaredNotFree(SchemaVariable var) {
       for (final NotFreeIn nfi : varsNotFreeIn) {
          if (nfi.first() == var) {
             return true;
          }
       }
       return false;
    }


    /**
     * returns true iff the given variable is bound either in the
     * ifSequent or in 
     * any part of the TacletGoalTemplates
     * @param v the bound variable to be searched 
     */
    private boolean varIsBound(SchemaVariable v) {
        return (v instanceof QuantifiableVariable) && boundVars.contains((QuantifiableVariable) v);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions checkVariableConditions(SchemaVariable var, 
            SVSubstitute instantiationCandidate,
            MatchConditions matchCond,
            Services services) {        
        if (matchCond != null) {
            if (instantiationCandidate instanceof Term) {
                final Term term = (Term) instantiationCandidate;
                if (!(term.op() instanceof QuantifiableVariable)) {
                    if (varIsBound(var) || varDeclaredNotFree(var)) {
                        // match(x) is not a variable, but the corresponding template variable is bound
                        // or declared non free (so it has to be matched to a variable)       
                        return null; // FAILED
                    }
                }
            }
            // check generic conditions
            for (final VariableCondition vc : varconditions) {
                matchCond = vc.check(var, instantiationCandidate, matchCond, services);       
                if (matchCond == null) {       
                    return null; // FAILED
                }
            }
        }
        return matchCond; 
    }
    
    /**
     * ignores a possible update prefix
     * @param term the term to be matched
     * @param template the pattern term
     * @param matchCond the accumulated match conditions for a successful match
     * @param services the Services
     * @return a pair of updated match conditions and the unwrapped term without the ignored updates (Which have been added to the update context in the match conditions)
     */
    private Pair<Term,MatchConditions> matchAndIgnoreUpdatePrefix(final Term term,
            final Term template, MatchConditions matchCond, final TermServices services) {

        final Operator sourceOp   = term.op ();
        final Operator templateOp = template.op ();

        if ( sourceOp instanceof UpdateApplication
                && !(templateOp instanceof UpdateApplication) ) {
            // updates can be ignored
            Term update = UpdateApplication.getUpdate(term);
            matchCond = matchCond
                    .setInstantiations ( matchCond.getInstantiations ().
                            addUpdate (update, term.getLabels()) );
            return matchAndIgnoreUpdatePrefix(UpdateApplication.getTarget(term), 
                    template, matchCond, services);       
        } else {
            return new Pair<Term, MatchConditions>(term, matchCond);
        }
    }

    
    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions matchFind(Term term, 
            MatchConditions matchCond,
            Services services) {
        
        if (findExp != null) {
            if (ignoreTopLevelUpdates) {
                Pair</* term below updates */Term, MatchConditions> resultUpdateMatch = 
                        matchAndIgnoreUpdatePrefix(term, findExp, matchCond, services);
                term = resultUpdateMatch.first;
                matchCond = resultUpdateMatch.second;
            }
            matchCond = checkConditions(match(term, findMatchProgram, matchCond, services), services); 
        } else {
            matchCond = null;
        }
        
        return matchCond; 
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
            do {
                MutablePair<Term, Integer> el = stack.peek();            
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
