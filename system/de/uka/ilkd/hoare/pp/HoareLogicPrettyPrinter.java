package de.uka.ilkd.hoare.pp;

import java.io.IOException;

import de.uka.ilkd.hoare.rule.HoareLoopInvRuleApp;
import de.uka.ilkd.hoare.rule.HoareLoopInvariantRule;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.util.pp.Backend;
import de.uka.ilkd.key.util.pp.Layouter;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;

/**
 * The HoareLogic PrettyPrinter displays the sequent as a hoare triple. 
 * It makes some basic and important assumptions:
 * <ul>
 * <li> there is maximal one formula containg a program </li>
 * <li> if a formula contains a program, teh program occurs in the succedent </li>
 * <li> a program occurs always inside a box modality </li>
 * <li> a formula containing a program has always teh shape <tt>U \[ prg \] phi</tt>
 * </ul>
 */
public class HoareLogicPrettyPrinter extends LogicPrinter {

    private static final String HOARE_TRIPLE_UPDATE_SECTION_END = "]";

    private static final String HOARE_TRIPLE_UPDATE_SECTION_START = "[";

    /**
     * The standard concrete syntax for terms with updates.
     */
    public static class QuanUpdate extends Notation {

        public QuanUpdate() {
            super(115);
        }

        public void print(Term t, LogicPrinter sp) throws IOException {
            if (sp.getNotationInfo().getAbbrevMap().isEnabled(t)) {
                sp.printTerm(t);
            } else {
                final Operator targetOp = ((IUpdateOperator) t.op()).target(t)
                        .op();
                final int assTarget = (t.sort() == Sort.FORMULA ? (targetOp
                        .arity() == 1 ? 60 : 85) : 110);
                if (t.op() instanceof AnonymousUpdate) {
                    sp.printAnonymousUpdate(t, assTarget);
                } else {
                    sp.printQuanUpdateTerm(HOARE_TRIPLE_UPDATE_SECTION_START,
                            ":=", HOARE_TRIPLE_UPDATE_SECTION_END, t, 80, 0,
                            assTarget);
                }
            }
        }
    }

    private static final String SEMI_SEQ_SEP_ANTEC = " & ";

    private static final String SEMI_SEQ_SEP_SUCC = " | ";

    private boolean previousPrintedOpWasQuanUpdate;

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo, Backend backend, Services services) {
        super(prgPrinter, notationInfo, backend, services);
        tweakNotationInfo(notationInfo, services);
    }

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo, Backend backend, Services services,
            boolean purePrint) {
        super(prgPrinter, notationInfo, backend, services, purePrint);
        tweakNotationInfo(notationInfo, services);
    }

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo, Services services) {
        super(prgPrinter, notationInfo, services);
        tweakNotationInfo(notationInfo, services);
    }

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter,
            NotationInfo notationInfo, Services services, boolean purePrint) {
        super(prgPrinter, notationInfo, services, purePrint);
        tweakNotationInfo(notationInfo, services);
    }

    /** returns the index of the first formula containing a program or <tt>-1</tt>
     * if no such formula exists
     * @param it the IteratorOfConstrainedFormula to search through
     * @return the index of the formula containing a program or <tt>-1</tt>
     */
    private int findProgramFormula(IteratorOfConstrainedFormula it) {
        int idx = 0;

        while (it.hasNext()) {
            final ConstrainedFormula cf = it.next();
            if (hasProgram(cf.formula())) {
                return idx;
            }
            idx++;
        }
        return -1;
    }

    /** returns the index of the first formula containing an update on top level 
     * or <tt>-1</tt> if no such formula exists
     * @param it the IteratorOfConstrainedFormula to search through
     * @return the index of the formula containing an update or <tt>-1</tt>
     */
    private int findUpdateFormula(IteratorOfConstrainedFormula it) {
        int idx = 0;

        while (it.hasNext()) {
            final ConstrainedFormula cf = it.next();
            if (cf.formula().op() instanceof QuanUpdateOperator) {
                return idx;
            }
            idx++;
        }
        return -1;
    }

    /**
     * returns if a formula contains a program. Attention: the implementation 
     * makes heavy usage of the assumptions stated in the class comment
     * @param formula
     * @return true if the formula contains a program
     */
    private boolean hasProgram(Term formula) {
        final Operator op = formula.op();
        if (formula.sort() != Sort.FORMULA) {
            return false;
        } else if (op instanceof Modality || op instanceof ModalOperatorSV) {
            return true;
        }
        assert !(op instanceof Modality || op instanceof ModalOperatorSV) : "Hoare Tuple Normalform hurt.";

        if (op instanceof QuanUpdateOperator) {
            return hasProgram(((QuanUpdateOperator) op).target(formula));
        }

        return false;
    }

    public void printCast(String pre, String post, Term t, int ass)
            throws IOException {
        startTerm(t.arity());
        //markStartSub();
        maybeParens(t.sub(0), ass);
        //printTerm(t.sub(0));
        //markEndSub();
    }

    private void printConditional(ProgramElement guard, ProgramElement thenS,
            ProgramElement elseS) throws IOException {
        layouter.beginC().print("if (");
        printProgramElement(guard);
        layouter.print(")").brk();
        layouter.beginC(2);

        printProgramElement(thenS);
        layouter.end();

        layouter.brk();

        layouter.beginC(2).print("else").brk(1);
        printProgramElement(elseS);
        layouter.end();

        layouter.brk();

        layouter.print("s").brk(2).end();
    }

    private void printHoarePost() throws IOException {
        layouter.beginC(2).print("{").print("Q").print("}").brk(1).end();
    }

    private void printHoarePreconditon() throws IOException {
        printHoarePreconditon("P", new Term[0]);
    }

    private void printHoarePreconditon(String prefix, Term[] add)
            throws IOException {
        layouter.beginC(2).print("{").print(prefix);
        for (int i = 0; i < add.length; i++) {
            layouter.brk(1).print("&").brk(1);
            printTerm(add[i]);
        }
        layouter.print("}").brk(2).end();
    }

    /**
     * Print a Java block.  This is formatted using the ProgramPrinter
     * given to the constructor.  The result is indented according to
     * the surrounding material.  The first `executable' statement is
     * marked for highlighting.
     *
     * @param j the Java block to be printed
     */
    public void printHoareProgramBlock(JavaBlock j) throws IOException {
        java.io.StringWriter sw = new java.io.StringWriter();
        prgPrinter.reset();
        prgPrinter.setWriter(sw);
        Range r = null;
        try {
            j.program().prettyPrint(prgPrinter);
            r = prgPrinter.getRangeOfFirstExecutableStatement();
        } catch (java.io.IOException e) {
            layouter.print("ERROR");
            System.err.println("Error while printing Java program \n" + e);
            throw new RuntimeException("Error while printing Java program \n"
                    + e);
        }
        // send first executable statement range
        String s = sw.toString().replaceFirst("\\{", " ");
        s = s.substring(0, s.lastIndexOf('}')) + " ";
        printMarkingFirstStatement(s, r);
    }

    private void printHoareUpdate(String update) throws IOException {
        printHoareUpdate(update, null, null);
    }

    private void printHoareUpdate(String update, ProgramElement location,
            ProgramElement value) throws IOException {
        layouter.beginI(2);

        layouter.print(HOARE_TRIPLE_UPDATE_SECTION_START + update);
        if (location != null) {
            layouter.print(",").brk(1);
            if (services != null) {
                printTerm(services.getTypeConverter().convertToLogicElement(
                        location));
                layouter.print(":=");
                printTerm(services.getTypeConverter().convertToLogicElement(
                        value));
            } else {
                printProgramElement(location);
                layouter.print(":=");
                printProgramElement(value);
            }
        }
        layouter.print(HOARE_TRIPLE_UPDATE_SECTION_END).brk(1);

        layouter.end();
    }

    private void printIfConclusion(final ProgramElement guard,
            final ProgramElement thenS, final ProgramElement elseS)
            throws IOException {
        layouter.beginI(2);
        printHoarePreconditon();
        printHoareUpdate("U");
        printConditional(guard, thenS, elseS);
        printHoarePost();
        layouter.end();
    }

    private void printIfElse(final ProgramElement guard,
            final ProgramElement elseS, boolean wcet) throws IOException {
        layouter.beginI(2);
        printHoarePreconditon("P", new Term[] { TermBuilder.DF.not(services
                .getTypeConverter().convertToLogicElement(guard)) });
        printHoareUpdate("U"
                + (wcet ? ", executionTime := executionTime + 1" : ""));

        layouter.beginC(2);
        printProgramElement(elseS);
        layouter.brk();
        layouter.print("s").brk(2);
        layouter.end();

        printHoarePost();
        layouter.end();
    }

    private void printIfThen(final ProgramElement guard,
            final ProgramElement thenS, boolean wcet) throws IOException {
        layouter.beginI(2);
        printHoarePreconditon("P", new Term[] { services.getTypeConverter()
                .convertToLogicElement(guard) });
        printHoareUpdate("U"
                + (wcet ? ", executionTime := executionTime + 1" : ""));

        layouter.beginC(2);
        printProgramElement(thenS);
        layouter.brk();
        layouter.print("s").brk(2, 0);
        layouter.end();

        printHoarePost();
        layouter.end();
    }

    public void printNormalSequent(Sequent seq, boolean finalbreak) {
        try {
            Semisequent antec = seq.antecedent();
            Semisequent succ = seq.succedent();
            markStartSub();
            startTerm(antec.size() + succ.size());
            layouter.beginC(0).ind();
            layouter.print("|-").brk(1, 2);

            boolean formulaInAntec = antec.size() > 0;

            printSemisequent(antec, true, false);

            if (succ.size() > 0) {
                final int idx = findUpdateFormula(succ.iterator());

                if (idx >= 0) {
                    if (antec.size() > 0) {
                        if (succ.size() > 1) {
                            layouter.print(SEMI_SEQ_SEP_ANTEC).brk(1);
                        }
                    }
                    formulaInAntec = formulaInAntec || succ.size() > 1;
                    printSemisequent(succ.remove(idx).semisequent(), false,
                            true);
                }
                if (formulaInAntec)
                    layouter.brk(1, -1).print("->").brk(1, 2);
                if (idx >= 0) {
                    markStartSub();
                    printConstrainedFormula(succ.get(idx));
                    markEndSub();
                } else {
                    printSemisequent(succ, false, false);
                }
            }
            if (finalbreak) {
                layouter.brk(0);
            }
            markEndSub();
            layouter.end();
        } catch (IOException e) {
            throw new RuntimeException("IO Exception in pretty printer:\n" + e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException("Unbalanced blocks in pretty printer:\n"
                    + e);
        }
    }

    private void printProgramFormula(int idx, final Semisequent succ)
            throws IOException {
        Term programFormula = succ.get(idx).formula();

        layouter.brk();

        layouter.beginC(0).print(HOARE_TRIPLE_UPDATE_SECTION_START);
        int count = 0;
        while (programFormula.op() instanceof QuanUpdateOperator) {
            startTerm(programFormula.arity());
            printQuanPrefix(programFormula);
            programFormula = ((QuanUpdateOperator) programFormula.op())
                    .target(programFormula);
            count++;
            if (programFormula.op() instanceof QuanUpdateOperator) {
                layouter.print(", ");
                markStartSub();
            }
        }
        layouter.print(HOARE_TRIPLE_UPDATE_SECTION_END).end().brk();

        if (count > 0) {
            // avoids ')' to be highlighted when selecting program
            markStartSub();
        }

        mark(MARK_MODPOSTBL);
        startTerm(programFormula.arity());

        printHoareProgramBlock(programFormula.javaBlock());

        layouter.brk(0);

        layouter.beginC(0).print("{").brk(1);

        markStartSub(); //start post
        printTerm(programFormula.sub(0));
        markEndSub();// end post           

        layouter.brk(1).print("}").end();

        layouter.brk();

        for (int i = 0; i < count; i++) {
            markEndSub();
        }

        layouter.end();
    }

    private void printQuanPrefix(Term term) throws IOException {
        Term t = term;
        final QuanUpdateOperator op = (QuanUpdateOperator) t.op();
        layouter.beginC(2);
        for (int i = 0; i < op.locationCount(); i++) {
            final Operator loc = op.location(i);

            layouter.beginC(0);
            printUpdateQuantification(t, op, i);

            final String[] separator = setupUpdateSeparators(loc, op.location(
                    t, i));
            for (int j = loc.arity(); j >= 1; j--) {
                final Term sub = t.sub(op.valuePos(i) - j);
                markStartSub();
                printTerm(sub);
                markEndSub();
                layouter.print(separator[loc.arity() - j]);

            }
            layouter.print(":=").brk(0, 0);
            layouter.end();
            maybeParens(op.value(t, i), 0);
            if (i < op.locationCount() - 1) {
                layouter.print(" ||").brk(1, 0);
            }
        }
        layouter.end();
    }

    /**
     * Print a term with an (quantified) update.  This looks like
     * <code>{loc1 := val1 || ... || locn := valn} t</code>.  If line breaks are necessary, the
     * format is
     *
     * <pre>
     * {loc1:=val1 || ... || locn:=valn}
     *   t
     * </pre>
     *
     * @param l       the left brace
     * @param asgn    the assignment operator (including spaces)
     * @param r       the right brace
     * @param t       the update term
     * @param ass1    associativity for the locations
     * @param ass2    associativity for the new values
     * @param ass3    associativity for phi
     */
    public void printQuanUpdateTerm(String l, String asgn, String r, Term t,
            int ass1, int ass2, int ass3) throws IOException {
        final QuanUpdateOperator op = (QuanUpdateOperator) t.op();
        layouter.beginC(2);
        if (!previousPrintedOpWasQuanUpdate) {
            layouter.print(l);
            previousPrintedOpWasQuanUpdate = false;
        }
        startTerm(t.arity());
        for (int i = 0; i < op.locationCount(); i++) {
            final Operator loc = op.location(i);

            layouter.beginC(0);
            printUpdateQuantification(t, op, i);

            final String[] separator = setupUpdateSeparators(loc, op.location(
                    t, i));
            for (int j = loc.arity(); j >= 1; j--) {
                final Term sub = t.sub(op.valuePos(i) - j);

                markStartSub();
                printTerm(sub);
                markEndSub();
                layouter.print(separator[loc.arity() - j]);
            }
            layouter.print(asgn).brk(0, 0);
            layouter.end();
            maybeParens(op.value(t, i), ass2);
            if (i < op.locationCount() - 1) {
                layouter.print(" ||").brk(1, 0);
            }
        }

        if (op.target(t).op() instanceof QuanUpdateOperator) {
            layouter.print(",").brk(1);
            previousPrintedOpWasQuanUpdate = true;
        } else {
            layouter.print(r).brk(0);
        }
        maybeParens(op.target(t), ass3);
        layouter.end();
    }

    public void printSemisequent(ListOfSequentPrintFilterEntry p_formulas,
            boolean antec) throws IOException {
        printSemisequent(p_formulas, antec, !antec);
    }

    public void printSemisequent(ListOfSequentPrintFilterEntry p_formulas,
            boolean antec, boolean succ2antec) throws IOException {

        IteratorOfSequentPrintFilterEntry it = p_formulas.iterator();
        SequentPrintFilterEntry entry;
        int size = p_formulas.size();
        while (size-- != 0) {
            entry = it.next();
            markStartSub();
            formulaConstraint = entry.getDisplayConstraint();
            if (succ2antec)
                layouter.print("!(");
            printConstrainedFormula(entry.getFilteredFormula());
            if (succ2antec)
                layouter.print(")");
            markEndSub();
            if (size != 0) {
                if (succ2antec || antec) {
                    layouter.print(SEMI_SEQ_SEP_ANTEC).brk(1);
                } else {
                    layouter.print(SEMI_SEQ_SEP_SUCC).brk(1);
                }
            }
        }
        formulaConstraint = null;
    }

    /**
     * Pretty-prints a Semisequent.  Formulae are separated by commas.
     *
     * @param semiseq the semisequent to be printed
     */
    public void printSemisequent(Semisequent semiseq, boolean antec)
            throws IOException {
        printSemisequent(semiseq, antec, !antec);
    }

    /**
     * Pretty-prints a Semisequent.  Formulae are separated by commas.
     *
     * @param semiseq the semisequent to be printed
     */
    public void printSemisequent(Semisequent semiseq, boolean antec,
            boolean succ2antec) throws IOException {
        for (int i = 0; i < semiseq.size(); i++) {
            markStartSub();
            if (succ2antec)
                layouter.print("!(");
            printConstrainedFormula(semiseq.get(i));
            if (succ2antec)
                layouter.print(")");
            markEndSub();
            if (i != semiseq.size() - 1) {
                if (succ2antec || antec) {
                    layouter.print(SEMI_SEQ_SEP_ANTEC).brk(1);
                } else {
                    layouter.print(SEMI_SEQ_SEP_SUCC).brk(1);
                }
            }
        }
    }

    public void printSequent(Sequent seq, boolean finalbreak) {
        final Semisequent succ = seq.succedent();
        final int idx = findProgramFormula(succ.iterator());
        if (idx >= 0) {
            markStartSub();
            printSequentAsHoareTriple(seq, finalbreak, idx);
            markEndSub();
        } else {
            printNormalSequent(seq, finalbreak);
        }
    }

    public void printSequent(SequentPrintFilter filter, boolean finalbreak) {
        printSequent(filter.getSequent());
    }

    private void printSequentAsHoareTriple(Sequent seq, boolean finalbreak,
            int idx) {
        try {
            final Semisequent antec = seq.antecedent();
            final Semisequent succ = seq.succedent();

            startTerm(antec.size() + succ.size());

            layouter.beginC(0).print("{");

            layouter.beginC(1).ind(1, 1);
            printSemisequent(antec, true, false);
            if (antec.size() > 0) {
                if (succ.size() > 1) {
                    layouter.print(SEMI_SEQ_SEP_ANTEC).brk(1);
                }
            }

            printSemisequent(succ.remove(idx).semisequent(), false, true);
            layouter.brk(1).print("}").end();

            layouter.brk();

            markStartSub(); // start program formula
            printProgramFormula(idx, succ);
            markEndSub(); //end program formula
        } catch (IOException e) {
            throw new RuntimeException("IO Exception in pretty printer:\n" + e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException("Unbalanced blocks in pretty printer:\n"
                    + e);
        }
    }

    private void printSimpleIfTaclet(final ProgramElement guard,
            final ProgramElement thenS, final ProgramElement elseS, boolean wcet)
            throws IOException {
        layouter.beginI(0);

        layouter.beginC(2);
        layouter.print("Then Branch:").brk(1);
        printIfThen(guard, thenS, wcet);
        layouter.end().nl();

        layouter.beginC(2);
        layouter.print("Else Branch:").brk(1);
        printIfElse(guard, elseS, wcet);
        layouter.end().nl();

        layouter.print("----").nl();

        layouter.beginC(2);
        layouter.print("Conclusion:").brk(1);
        printIfConclusion(guard, thenS, elseS);
        layouter.end();
        layouter.nl();

        layouter.end();
    }

    public void printTaclet(TacletApp t) {
        if (services == null) {
            super.printTaclet(t.taclet());
            return;
        }

        try {
            final String tacletName = t.taclet().name().toString();
            if (tacletName.equals("conditional")) {
                printTacletConditional(t.instantiations(), false);
            } else if (tacletName.equals("conditionalExecutionTime")) {
                printTacletConditional(t.instantiations(), true);
            } else if (tacletName.equals("assignment")) {
                printTacletAssignment(t.instantiations(), false);
            } else if (tacletName.equals("assignmentExecutionTime")) {
                printTacletAssignment(t.instantiations(), true);
            } else if (tacletName.equals("skip")) {
                printTacletSkip(t.instantiations(), false);
            } else if (tacletName.equals("skipExecutionTime")) {
                printTacletSkip(t.instantiations(), true);
            } else if (tacletName.equals("exit")) {
                printTacletExit(t.instantiations());
            } else {
                super.printTaclet(t.taclet());
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private void printTacletExit(SVInstantiations instantiations)
            throws IOException {
        layouter.beginC(0);
        layouter.print("P |- U(Q)").nl();
        layouter.print("---").nl();        
        layouter.print("C: {P} [U]  {Q}");
        
        layouter.nl().nl();
        
        printText("The exit rule is applicable when the complete program has been "
                + "symbolically executed. It remains then to show that the precondition implies"
                + "the post condition evaluated in the final state.");

        layouter.end();

    }

    public void printTacletAssignment(SVInstantiations svInst, boolean wcet)
            throws IOException {
        layouter.beginC(0);

        layouter.nl();

        printSimpleAssignmentTaclet(svInst, wcet);

        layouter.nl();

        printText("The assignment rule matches on a Hoare Triple whose first "
                + "statement is an assignment. The assignment is moved "
                + "outside into an update and sequential concatenated with the preceding update U.");

        layouter.nl();

        layouter.end();
    }

    private void printSimpleAssignmentTaclet(SVInstantiations svInst,
            boolean wcet) throws IOException {
        layouter.beginI(0);
        layouter.beginC(2);
        layouter.print("1:").brk(1);
        printTacletAssignmentPre(svInst, wcet);
        layouter.end().nl();

        layouter.print("----").nl();

        layouter.beginC(2);
        layouter.print("C:").brk(1);
        printTacletAssignmentConclusion(svInst);
        layouter.end();
        layouter.nl();
        layouter.end();
    }

    private void printTacletAssignmentPre(SVInstantiations svInst, boolean wcet)
            throws IOException {
        layouter.beginC(2);
        printHoarePreconditon();

        printHoareUpdate("U"
                + (wcet ? ", executionTime := executionTime + 1" : ""),
                (ProgramElement) svInst.lookupValue(new Name("#leftVar")),
                (ProgramElement) svInst.lookupValue(new Name("#rightExp")));

        layouter.beginC(2);
        layouter.print("s").brk(2, 0);
        layouter.end();
        printHoarePost();
        layouter.end();
    }

    private void printTacletAssignmentConclusion(SVInstantiations svInst)
            throws IOException {
        layouter.beginC(2);
        printHoarePreconditon();
        printHoareUpdate("U");

        layouter.beginC(2);
        printProgramElement((ProgramElement) svInst.lookupValue(new Name(
                "#leftVar")));
        layouter.brk(1).print("=").brk(1);
        printProgramElement((ProgramElement) svInst.lookupValue(new Name(
                "#rightExp")));
        layouter.print(";").brk();
        layouter.print("s").brk(2, 0);
        layouter.end();

        printHoarePost();
        layouter.end();
    }

    public void printTacletConditional(SVInstantiations svInst, boolean wcet)
            throws IOException {
        final ProgramElement guard = (ProgramElement) svInst
                .lookupValue(new Name("#guard"));
        final ProgramElement thenS = (ProgramElement) svInst
                .lookupValue(new Name("#thenStatement"));
        final ProgramElement elseS = (ProgramElement) svInst
                .lookupValue(new Name("#elseStatement"));

        layouter.beginC(0);

        layouter.nl();
        printSimpleIfTaclet(guard, thenS, elseS, wcet);
        layouter.nl();

        printText("The conditional rule matches on a Hoare Triple whose first "
                + "statement is an \"if-then-else\" statement:");

        layouter.nl();

        layouter.ind(0, 2);
        printIfConclusion(guard, thenS, elseS);

        layouter.nl().nl();

        printText("The proof splits up into two branches."
                + (wcet ? " The evaluation of the condition requires one time unit. This "
                        + "cost is reflected by increasing the executionTime counter."
                        : "") + "The first branch:");

        layouter.nl();

        layouter.ind(0, 2);
        printIfThen(guard, thenS, wcet);

        layouter.nl().nl();

        printText("treats the case where the \"if\"-condition is true. Thus only the \"then\" path "
                + "needs to be considered.");

        layouter.nl().nl();

        printText("The second branch treats the case when the \"if\"-condition "
                + "is false and only the \"else\" path of the conditional is executed:");

        layouter.nl();

        layouter.ind(0, 2);
        printIfElse(guard, elseS, wcet);

        layouter.nl().nl();

        layouter.end();
    }

    public void printTacletSkip(SVInstantiations svInst, boolean wcet)
            throws IOException {
        layouter.beginC(0);

        printText("The skip rule matches on a Hoare Triple whose first "
                + "statement is an empty statement:");

        layouter.nl();

        layouter.beginI(2).nl();
        printHoarePreconditon();
        printHoareUpdate("U");

        layouter.beginC(2);
        layouter.print(";").brk();
        layouter.print("s").brk(2, 0);
        layouter.end();

        printHoarePost();
        layouter.end();

        layouter.nl().nl();

        if (!wcet) {
            printText("The empty statement has no effect at all and can be simply removed:");
        } else {
            printText("Execution of the empty statement costs one time unit, but has no"
                    + " further effect. The cost is refelected by increasing the executionTime counter.");
        }

        layouter.nl();

        layouter.beginI(2).nl();
        printHoarePreconditon();

        printHoareUpdate(wcet ? "U, executionTime := executionTime+1" : "U");

        layouter.beginC(2);
        layouter.print("s").brk(2, 0);
        layouter.end();
        printHoarePost();
        layouter.end();

        layouter.nl().nl();

        layouter.end();
    }

    private Sequent constructSequent(Term[] antec, Term succ) {
        Semisequent antecSemi = Semisequent.EMPTY_SEMISEQUENT;
        for (int i = antec.length - 1; i >= 0; i--) {
            antecSemi = antecSemi.insertFirst(new ConstrainedFormula(antec[i]))
                    .semisequent();
        }
        return Sequent.createSequent(antecSemi, Semisequent.EMPTY_SEMISEQUENT
                .insertFirst(new ConstrainedFormula(succ)).semisequent());
    }

    private static final Function P = new RigidFunction(new Name("P"),
            Sort.FORMULA, new Sort[0]);

    private static final Term PT = TermBuilder.DF.func(P);

    private static final Function Q = new RigidFunction(new Name("Q"),
            Sort.FORMULA, new Sort[0]);

    private static final Term QT = TermBuilder.DF.func(Q);

    public void printWhileRule(HoareLoopInvRuleApp ra) throws IOException {
        final Layouter l = layouter;

        final HoareLoopInvariantRule invRule = (HoareLoopInvariantRule) ra
                .rule();
        final Term condition = invRule.getCondition(ra, services);
        final Term inv = ra.getInvariant();
        final Term decreases = ra.getDecreases();
        final TermBuilder tb = TermBuilder.DF;
        final Term oldDecreases = decreases != null ? tb
                .func(new RigidFunction(ra.getDecreaseAtPreFuncName(),
                        decreases.sort(), new Sort[0])) : null;

        final Term decreaseGEQZero = decreases != null ? tb.geq(decreases, tb
                .zero(services), services) : null;

        Statement loopBodyS = invRule.getWhileStatement(ra).getBody();
        if (!(loopBodyS instanceof StatementBlock)) {
            loopBodyS = new StatementBlock(loopBodyS);
        }
        final JavaBlock loopBody = JavaBlock
                .createJavaBlock((StatementBlock) loopBodyS);

        final Update origUpdateU = Update.createUpdate(ra.posInOccurrence()
                .constrainedFormula().formula());
        final UpdateFactory uf = new UpdateFactory(services, null);

        l.beginI(0);

        l.beginI(2);
        l.print("Invariant Initially Valid:").brk(1);
        printInitialValidBranch(inv, decreases, tb, decreaseGEQZero,
                origUpdateU, uf);
        l.nl();
        printText("The initial valid branch ensures that the provided invariant ");
        l.brk(1).print("\"");
        printTerm(inv);
        l.print("\"").brk(1);
        printText("is valid before the loop is executed for the first time.");

        layouter.nl();
        if (decreases != null) {
            printText(" In order to prove termination one has to show "
                    + "that the user provided term");
            l.brk(1).print("\"");
            printTerm(decreases);
            l.print("\"").brk(1);
            printText("is non-negative and decreases strict monotonous. In the initial case "
                    + "it is sufficient to show that the term is non-negative in the "
                    + "beginning.");
        }

        l.end();
        l.nl().nl();

        l.beginI(2);
        l.print("Preserve Invariant:").brk(1);
        printPreserveBranch(ra, invRule, condition, inv, decreases, tb,
                oldDecreases, decreaseGEQZero, loopBody, uf);
        l.nl();
        printText("The preserves branch ensures that in any state satisfying the invariant");
        l.brk(1).print("\"");
        printTerm(inv);
        l.print("\"").brk(1);
        printText("and the loop condition");
        l.brk(1).print("\"");
        printTerm(condition);
        l.print("\"").brk(1);
        printText("then the invariant holds again after one loop iteration. As the "
                + "loop iteration is executed in an arbitrary but fixed state, "
                + "one has to remove the original preconditon P and the original update.");
        layouter.nl();
        if (decreases != null) {
            printText("In order to prove termination one has to show that "
                    + "the user provided term");
            l.brk(1).print("\"");
            printTerm(decreases);
            l.print("\"").brk(1);
            printText("is non-negative and decreases strict monotonous. "
                    + "The non-negative part is the same as in the initial case, "
                    + "but here one has also to prove the monotone decreasing part. "
                    + "Therefore the old value is captured in the precondition by "
                    + "the introduction of an unused function which evaluates to the "
                    + "value of the decreasing term in the prestate.");
        }
        layouter.nl();
        if (invRule.modus(ra.posInOccurrence()) == Op.DIATRC) {
            printText("The executionTime counter is increased as the evaluation of the"
                    + "loop condition costs one time unit.");
        }
        l.end();

        l.nl().nl();

        l.beginC(2);
        l.print("Use Case:").brk(1);
        printUseBranch(ra, invRule, condition, inv, tb, uf);
        l.nl();
        printText("This branch treats the case when the loop is left. "
                + "It remains to show that for any state satisfying the invariant and where the loop"
                + "condition evaluates to false, the original postcondition holds after "
                + "the execution of the remaining program.");
        layouter.nl();
        if (invRule.modus(ra.posInOccurrence()) == Op.DIATRC) {
            printText("The executionTime counter is increased as the evaluation of the"
                    + "loop condition costs one time unit.");
        }
        l.end();
        l.nl();
        l.print("---");
        l.nl();
        l.beginC(2);
        l.print("Conclusion:").brk(1);
        Term[] antecConcl = new Term[] { PT };
        Term succConcl = uf.prepend(origUpdateU, tb.tf().createProgramTerm(
                invRule.modus(ra.posInOccurrence()),
                invRule.getModalityTerm(ra.posInOccurrence()).javaBlock(), QT));
        printSequent(constructSequent(antecConcl, succConcl));
        l.end();

        l.end();
    }

    private void printInitialValidBranch(final Term inv, final Term decreases,
            final TermBuilder tb, final Term decreaseGEQZero,
            final Update origUpdateU, final UpdateFactory uf) {
        final Term[] antecInitial = new Term[] { PT };

        Term succInitial = inv;
        if (decreases != null) {
            succInitial = tb.and(succInitial, decreaseGEQZero);
        }
        succInitial = uf.prepend(origUpdateU, succInitial);

        Sequent seq = constructSequent(antecInitial, succInitial);
        printSequent(seq);
    }

    private void printUseBranch(HoareLoopInvRuleApp ra,
            final HoareLoopInvariantRule invRule, final Term condition,
            final Term inv, final TermBuilder tb, final UpdateFactory uf) {
        final Term[] antecUse = new Term[] { inv, tb.not(condition) };

        Term succUse = QT;

        succUse = tb.tf().createProgramTerm(
                invRule.modus(ra.posInOccurrence()),
                invRule.getProgramAfterLoop(originalProgram(ra, invRule)),
                succUse);

        if (invRule.modus(ra.posInOccurrence()) == Op.DIATRC) {
            succUse = incExecutionTime(tb, uf, succUse);
        }

        printSequent(constructSequent(antecUse, succUse));
    }

    private void printPreserveBranch(HoareLoopInvRuleApp ra,
            final HoareLoopInvariantRule invRule, final Term condition,
            final Term inv, final Term decreases, final TermBuilder tb,
            final Term oldDecreases, final Term decreaseGEQZero,
            final JavaBlock loopBody, final UpdateFactory uf) {
        final Term[] antecPreserve;
        if (ra.getDecreases() == null) {
            antecPreserve = new Term[] { inv, condition };
        } else {
            antecPreserve = new Term[] { inv, condition,
                    tb.equals(oldDecreases, decreases), decreaseGEQZero };
        }

        Term succPreserve = inv;

        if (decreases != null) {
            succPreserve = tb.and(succPreserve, tb.lt(decreases, oldDecreases,
                    services));
        }

        succPreserve = tb.tf().createProgramTerm(
                invRule.modus(ra.posInOccurrence()), loopBody, succPreserve);

        if (invRule.modus(ra.posInOccurrence()) == Op.DIATRC) {
            succPreserve = incExecutionTime(tb, uf, succPreserve);
        }

        printSequent(constructSequent(antecPreserve, succPreserve));
    }

    private Term incExecutionTime(final TermBuilder tb, final UpdateFactory uf,
            Term succPreserve) {
        Term et = tb.func((Function) services.getNamespaces().functions()
                .lookup(HoareLoopInvariantRule.EXECTIME));
        final Function addF = services.getTypeConverter().getIntegerLDT().getAdd();
        final Update etPlusOne = uf.elementaryUpdate(et, tb.func(addF, et, tb
                .one(services)));
        succPreserve = uf.prepend(etPlusOne, succPreserve);
        return succPreserve;
    }

    private JavaProgramElement originalProgram(HoareLoopInvRuleApp ra,
            final HoareLoopInvariantRule invRule) {
        return invRule.getModalityTerm(ra.posInOccurrence()).javaBlock()
                .program();
    }

    public void printText(String s) throws IOException {
        layouter.beginI(0);
        final String[] chunks = s.split(" ");
        for (int i = 0; i < chunks.length; i++) {
            layouter.print(chunks[i]).brk(1);
        }
        layouter.end();
    }

    private void tweakNotationInfo(NotationInfo notInfo, Services services) {
        if (services == null)
            return;
        PresentationFeatures.putPrefixNotation(notInfo, services
                .getNamespaces().functions(), "javaUnaryMinusInt", "-");
        PresentationFeatures.putPrefixNotation(notInfo, services
                .getNamespaces().functions(), "javaUnaryMinusLong", "-");
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaAddInt", "+", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaAddLong", "+", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaSubInt", "-", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaSubLong", "-", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaMulInt", "*", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaMulLong", "*", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaDivInt", "/", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaDivLong", "/", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces()
                .functions(), "javaMod", "%", 100, 100, 101);

        notInfo.put(QuanUpdateOperator.class, new QuanUpdate());
    }

}
