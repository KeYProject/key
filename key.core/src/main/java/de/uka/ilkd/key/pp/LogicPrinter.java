/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.Iterator;
import java.util.Set;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.Notation.HeapConstructorNotation;
import de.uka.ilkd.key.pp.Notation.ObserverNotation;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import de.uka.ilkd.key.util.UnicodeHelper;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.pp.PosTableLayouter.DEFAULT_LINE_WIDTH;


/**
 * The front end for the Sequent pretty-printer. It prints a sequent and its parts and computes the
 * PositionTable, which is needed for highlighting.
 *
 * <p>
 * The actual layouting/formatting is done using the {@link de.uka.ilkd.key.util.pp.Layouter} class.
 * The concrete syntax for operators is given by an instance of {@link NotationInfo}. The
 * LogicPrinter is responsible for the concrete <em>layout</em>, e.g. how terms with infix operators
 * are indented, and it binds the various needed components together.
 *
 * @see NotationInfo
 * @see Notation
 * @see de.uka.ilkd.key.util.pp.Layouter
 */
public class LogicPrinter {
    private static final Logger LOGGER = LoggerFactory.getLogger(LogicPrinter.class);

    /**
     * Contains information on the concrete syntax of operators.
     */
    protected final NotationInfo notationInfo;

    /**
     * the services object
     */
    protected final Services services;

    /**
     * This chooses the layout.
     */
    protected PosTableLayouter layouter;

    private SVInstantiations instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;

    private final SelectPrinter selectPrinter;
    private final StorePrinter storePrinter;

    private QuantifiableVariablePrintMode quantifiableVariablePrintMode =
        QuantifiableVariablePrintMode.NORMAL;

    private enum QuantifiableVariablePrintMode {
        NORMAL, WITH_OUT_DECLARATION
    }

    /**
     * Creates a LogicPrinter. Sets the sequent to be printed, as well as a ProgramPrinter to print
     * Java programs and a NotationInfo which determines the concrete syntax.
     *
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param services services.
     * @param layouter the layouter to use
     */
    public LogicPrinter(NotationInfo notationInfo, Services services, PosTableLayouter layouter) {
        this.notationInfo = notationInfo;
        this.services = services;
        if (services != null) {
            notationInfo.refresh(services);
        }
        storePrinter = new StorePrinter(this.services);
        selectPrinter = new SelectPrinter(this.services);
        this.layouter = layouter;
    }

    /**
     * Creates a LogicPrinter that does not create a position table.
     *
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param services The Services object
     */
    public static LogicPrinter purePrinter(NotationInfo notationInfo, Services services) {
        return new LogicPrinter(notationInfo, services, PosTableLayouter.pure());
    }

    /**
     * @return the Layouter
     */
    public PosTableLayouter layouter() {
        return layouter;
    }

    private static SequentViewLogicPrinter quickPrinter(Services services,
            boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        final NotationInfo ni = new NotationInfo();
        if (services != null) {
            ni.refresh(services, usePrettyPrinting, useUnicodeSymbols);
        }

        // Use a SequentViewLogicPrinter instead of a plain LogicPrinter,
        // because the SequentViewLogicPrinter respects default TermLabel visibility
        // settings.
        return SequentViewLogicPrinter.purePrinter(ni, services, new TermLabelVisibilityManager());
    }

    /**
     * Converts a term to a string.
     *
     * @param t a term.
     * @param services services.
     * @return the printed term.
     */
    public static String quickPrintTerm(Term t, Services services) {
        return quickPrintTerm(t, services, NotationInfo.DEFAULT_PRETTY_SYNTAX,
            NotationInfo.DEFAULT_UNICODE_ENABLED);
    }

    /**
     * Converts a term to a string.
     *
     * @param t a term.
     * @param services services.
     * @param usePrettyPrinting whether to use pretty-printing.
     * @param useUnicodeSymbols whether to use unicode symbols.
     * @return the printed term.
     */
    public static String quickPrintTerm(Term t, Services services, boolean usePrettyPrinting,
            boolean useUnicodeSymbols) {
        var p = quickPrinter(services, usePrettyPrinting, useUnicodeSymbols);
        p.printTerm(t);
        return p.result();
    }

    /**
     * Converts a semisequent to a string.
     *
     * @param s a semisequent.
     * @param services services.
     * @return the printed semisequent.
     */
    public static String quickPrintSemisequent(Semisequent s, Services services) {
        var p = quickPrinter(services, NotationInfo.DEFAULT_PRETTY_SYNTAX,
            NotationInfo.DEFAULT_UNICODE_ENABLED);
        p.printSemisequent(s);
        return p.result();
    }

    /**
     * Converts a sequent to a string.
     *
     * @param s a sequent.
     * @param services services.
     * @return the printed sequent.
     */
    public static String quickPrintSequent(Sequent s, Services services) {
        var p = quickPrinter(services, NotationInfo.DEFAULT_PRETTY_SYNTAX,
            NotationInfo.DEFAULT_UNICODE_ENABLED);
        p.printSequent(s);
        return p.result();
    }

    /**
     * @return the notationInfo associated with this LogicPrinter
     */
    public NotationInfo getNotationInfo() {
        return notationInfo;
    }

    /**
     * Resets the printer by creating a new layouter.
     */
    public void reset() {
        layouter = layouter.cloneArgs();
    }

    /**
     * sets the line width to the new value but does <em>not</em> reprint the sequent. The actual
     * set line width is the maximum of {@link PosTableLayouter#DEFAULT_LINE_WIDTH} and the given
     * value
     *
     * @param lineWidth the max. number of character to put on one line
     */
    public void setLineWidth(int lineWidth) {
        this.layouter.setLineWidth(Math.max(lineWidth, DEFAULT_LINE_WIDTH));
    }

    /**
     * Reprints the sequent. This can be useful if settings like PresentationFeatures or
     * abbreviations have changed.
     *
     * @param filter The SequentPrintFilter for seq
     * @param lineWidth the max. number of character to put on one line (the actual taken linewidth
     *        is the max of {@link PosTableLayouter#DEFAULT_LINE_WIDTH} and the given value
     */
    public void update(SequentPrintFilter filter, int lineWidth) {
        setLineWidth(lineWidth);
        reset();
        if (filter != null) {
            printFilteredSequent(filter);
        }
    }

    /**
     * sets instantiations of schema variables
     */
    public void setInstantiation(SVInstantiations instantiations) {
        this.instantiations = instantiations;
    }

    /**
     * Pretty-print a taclet. Line-breaks are taken care of.
     *
     * @param taclet The Taclet to be pretty-printed.
     * @param sv The instantiations of the SchemaVariables
     * @param showWholeTaclet Should the find, varcond and heuristic part be pretty-printed?
     * @param declareSchemaVars Should declarations for the schema variables used in the taclet be
     *        pretty-printed?
     */
    public void printTaclet(Taclet taclet, SVInstantiations sv, boolean showWholeTaclet,
            boolean declareSchemaVars) {
        instantiations = sv;
        quantifiableVariablePrintMode = QuantifiableVariablePrintMode.WITH_OUT_DECLARATION;

        layouter.beginC();
        if (showWholeTaclet) {
            layouter.print(taclet.name().toString()).print(" {");
        }
        if (declareSchemaVars) {
            Set<SchemaVariable> schemaVars = taclet.collectSchemaVars();
            for (SchemaVariable schemaVar : schemaVars) {
                layouter.nl();
                schemaVar.layout(layouter);
                layouter.print(";");
            }
            layouter.nl();
        }
        if (!(taclet.ifSequent().isEmpty())) {
            printTextSequent(taclet.ifSequent(), "\\assumes");
        }
        if (showWholeTaclet) {
            printFind(taclet);
            if (taclet instanceof RewriteTaclet) {
                printRewriteAttributes((RewriteTaclet) taclet);
            }
            printVarCond(taclet);
        }
        printGoalTemplates(taclet);
        if (showWholeTaclet) {
            printHeuristics(taclet);
            printTriggers(taclet);
        }
        printAttribs(taclet);
        if (showWholeTaclet) {
            printDisplayName(taclet);
        }
        if (showWholeTaclet) {
            layouter.brk(1, -2).print("}");
        }
        layouter.end();
        instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        quantifiableVariablePrintMode = QuantifiableVariablePrintMode.NORMAL;
    }

    /**
     * Pretty-print a taclet. Line-breaks are taken care of. No instantiation is applied.
     *
     * @param taclet The Taclet to be pretty-printed.
     */
    public void printTaclet(Taclet taclet) {
        // the last argument used to be false. Changed that - M.Ulbrich
        printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true, true);
    }

    protected HeapLDT getHeapLDT() {
        return services == null ? null : services.getTypeConverter().getHeapLDT();
    }

    protected void printAttribs(Taclet taclet) {
        // no attributes exist for non-rewrite taclets at the moment
    }

    protected void printDisplayName(Taclet taclet) {
        final String displayName = taclet.displayName();
        if (displayName.equals(taclet.name().toString())) {
            // this means there is no special display name
            return;
        }
        layouter.nl().beginC().print("\\displayname " + '\"');
        layouter.print(displayName);
        layouter.print("" + '\"').end();
    }

    protected void printRewriteAttributes(RewriteTaclet taclet) {
        final int applicationRestriction = taclet.getApplicationRestriction();
        if ((applicationRestriction & RewriteTaclet.SAME_UPDATE_LEVEL) != 0) {
            layouter.nl().print("\\sameUpdateLevel");
        }
        if ((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) != 0) {
            layouter.nl().print("\\inSequentState");
        }
        if ((applicationRestriction & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
            layouter.nl().print("\\antecedentPolarity");
        }
        if ((applicationRestriction & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
            layouter.nl().print("\\succedentPolarity");
        }
    }

    protected void printVarCond(Taclet taclet) {
        final ImmutableList<NewVarcond> varsNew = taclet.varsNew();
        final ImmutableList<NewDependingOn> varsNewDependingOn = taclet.varsNewDependingOn();
        final ImmutableList<NotFreeIn> varsNotFreeIn = taclet.varsNotFreeIn();
        final ImmutableList<VariableCondition> variableConditions = taclet.getVariableConditions();

        if (!varsNew.isEmpty() || !varsNotFreeIn.isEmpty() || !variableConditions.isEmpty()
                || !varsNewDependingOn.isEmpty()) {
            layouter.nl().beginC().print("\\varcond(").brk(0);
            boolean first = true;

            for (NewDependingOn ndo : varsNewDependingOn) {
                if (first) {
                    first = false;
                } else {
                    layouter.print(",").brk();
                }
                printNewVarDepOnCond(ndo);
            }

            for (final NewVarcond nvc : varsNew) {
                if (first) {
                    first = false;
                } else {
                    layouter.print(",").brk();
                }
                printNewVarcond(nvc);
            }

            for (final NotFreeIn pair : varsNotFreeIn) {
                if (first) {
                    first = false;
                } else {
                    layouter.print(",").brk();
                }
                printNotFreeIn(pair);
            }

            for (final VariableCondition vc : variableConditions) {
                if (first) {
                    first = false;
                } else {
                    layouter.print(",").brk();
                }
                printVariableCondition(vc);
            }
            layouter.brk(0, -2).print(")").end();
        }
    }

    private void printNewVarDepOnCond(NewDependingOn on) {
        layouter.beginC(0);
        layouter.print("\\new(");
        printSchemaVariable(on.first());
        layouter.print(",").brk();
        layouter.print("\\dependingOn(");
        printSchemaVariable(on.second());
        layouter.brk(0, -2).print(")").brk();
        layouter.brk(0, -2).print(")").end();
    }

    protected void printNewVarcond(NewVarcond sv) {
        layouter.beginC();
        layouter.print("\\new(");
        printSchemaVariable(sv.getSchemaVariable());
        layouter.print(",").brk();
        if (sv.isDefinedByType()) {
            if (sv.getType() instanceof ArrayType) {
                layouter.print(((ArrayType) sv.getType()).getAlternativeNameRepresentation());
            } else {
                layouter.print(sv.getType().getFullName());
            }
        } else {
            layouter.print("\\typeof(").brk(0);
            printSchemaVariable(sv.getPeerSchemaVariable());
            layouter.brk(0, -2).print(")").brk(0);
        }
        layouter.brk(0, -2).print(")").end();
    }

    protected void printNotFreeIn(NotFreeIn sv) {
        layouter.beginI(0).print("\\notFreeIn(").brk(0);
        printSchemaVariable(sv.first());
        layouter.print(",").brk();
        printSchemaVariable(sv.second());
        layouter.brk(0, -2).print(")").end();
    }

    protected void printVariableCondition(VariableCondition sv) {
        layouter.print(sv.toString());
    }

    protected void printHeuristics(Taclet taclet) {
        if (taclet.getRuleSets().isEmpty()) {
            return;
        }
        layouter.nl().beginRelativeC().print("\\heuristics(").brk(0);
        for (Iterator<RuleSet> it = taclet.getRuleSets().iterator(); it.hasNext();) {
            RuleSet tgt = it.next();
            printHeuristic(tgt);
            if (it.hasNext()) {
                layouter.print(",").brk();
            }
        }
        layouter.end().print(")");
    }

    protected void printHeuristic(RuleSet sv) {
        layouter.print(sv.name().toString());
    }

    protected void printTriggers(Taclet taclet) {
        if (!taclet.hasTrigger()) {
            return;
        }
        layouter.nl().beginC().print("\\trigger {");
        Trigger trigger = taclet.getTrigger();
        printSchemaVariable(trigger.getTriggerVar());
        layouter.print("} ");
        printTerm(trigger.getTerm());
        if (trigger.hasAvoidConditions()) {
            Iterator<Term> itTerms = trigger.getAvoidConditions().iterator();
            layouter.brk(1, 2);
            layouter.print(" \\avoid ");
            while (itTerms.hasNext()) {
                Term cond = itTerms.next();
                printTerm(cond);
                if (itTerms.hasNext()) {
                    layouter.print(", ");
                }
            }
        }
        layouter.print(";").end();
    }

    protected void printFind(Taclet taclet) {
        if (!(taclet instanceof FindTaclet)) {
            return;
        }
        layouter.nl().beginC().print("\\find(").brk(0);
        if (taclet instanceof SuccTaclet) {
            printSequentArrow();
            layouter.brk();
        }
        layouter.beginRelativeC(1).ind();
        printTerm(((FindTaclet) taclet).find());
        layouter.end();
        if (taclet instanceof AntecTaclet) {
            layouter.brk(1);
            printSequentArrow();
        }
        layouter.brk(0, -2).print(")").end();
    }

    protected void printTextSequent(Sequent seq, String text) {
        layouter.nl();

        layouter.beginC().print(text).print("(").brk(0);
        if (seq != null) {
            printSequentInExistingBlock(seq);
        }
        layouter.brk(0, -2).print(")").end();
    }

    protected void printGoalTemplates(Taclet taclet) {
        if (taclet.closeGoal()) {
            layouter.nl().print("\\closegoal").brk();
        }

        for (final Iterator<TacletGoalTemplate> it = taclet.goalTemplates().reverse().iterator(); it
                .hasNext();) {
            printGoalTemplate(it.next());
            if (it.hasNext()) {
                layouter.print(";");
            }
        }
    }

    protected void printGoalTemplate(TacletGoalTemplate tgt) {
        // layouter.beginC(0);
        if (tgt.name() != null) {
            if (tgt.name().length() > 0) {
                layouter.nl().beginC().print("\"" + tgt.name() + "\"").print(":");
            }

        }
        if (tgt instanceof AntecSuccTacletGoalTemplate) {
            printTextSequent(((AntecSuccTacletGoalTemplate) tgt).replaceWith(), "\\replacewith");
        }
        if (tgt instanceof RewriteTacletGoalTemplate) {
            printRewrite(((RewriteTacletGoalTemplate) tgt).replaceWith());
        }

        if (!(tgt.sequent().isEmpty())) {
            printTextSequent(tgt.sequent(), "\\add");
        }
        if (!tgt.rules().isEmpty()) {
            printRules(tgt.rules());
        }
        if (tgt.addedProgVars().size() > 0) {
            layouter.nl();
            printAddProgVars(tgt.addedProgVars());
        }

        if (tgt.name() != null) {
            if (tgt.name().length() > 0) {
                layouter.end();
            }
        }
    }

    protected void printRules(ImmutableList<Taclet> rules) {
        layouter.nl().beginC().print("\\addrules(");
        SVInstantiations svi = instantiations;
        for (Taclet rule : rules) {
            layouter.nl();
            printTaclet(rule, instantiations, true, false);
            instantiations = svi;
        }
        layouter.brk(0, -2).print(")").end();
    }

    protected void printAddProgVars(ImmutableSet<SchemaVariable> apv) {
        layouter.beginC().print("\\addprogvars(");
        Iterator<SchemaVariable> it = apv.iterator();
        if (it.hasNext()) {
            layouter.brk();
            while (true) {
                SchemaVariable tgt = it.next();
                printSchemaVariable(tgt);
                if (it.hasNext()) {
                    layouter.print(",").brk();
                } else {
                    break;
                }
            }
        }
        layouter.brk(0, -2).print(")").end();
    }

    protected void printSchemaVariable(SchemaVariable sv) {
        Object o = getInstantiations().getInstantiation(sv);
        if (o == null) {
            if (sv instanceof ProgramSV) {
                printProgramSV((ProgramSV) sv);
            } else {
                printConstant(sv.name().toString());
            }
        } else {
            if (o instanceof Term) {
                printTerm((Term) o);
            } else if (o instanceof ProgramElement) {
                printProgramElement((ProgramElement) o);
            } else {
                LOGGER.error("Unknown instantiation type of {}; class is ", o.getClass().getName());
                printConstant(sv.name().toString());
            }
        }
    }

    private void printSourceElement(SourceElement element) {
        new PrettyPrinter(layouter, instantiations).print(element);
    }

    /**
     * Pretty-prints a ProgramElement.
     *
     * @param pe You've guessed it, the ProgramElement to be pretty-printedprint(Term t,
     *        LogicPrinter sp)
     */
    public void printProgramElement(ProgramElement pe) {
        if (pe instanceof ProgramVariable) {
            printProgramVariable((ProgramVariable) pe);
        } else {
            printSourceElement(pe);
        }
    }

    /**
     * Pretty-Prints a ProgramVariable in the logic, not in Java blocks. Prints out the full (logic)
     * name, so if A.b is private, it becomes a.A::b .
     *
     * @param pv The ProgramVariable in the logicprint(Term t, LogicPrinter sp)
     */
    public void printProgramVariable(ProgramVariable pv) {
        LOGGER.debug("PP PV {}", pv.name());
        layouter.beginC().print(pv.name().toString()).end();
    }

    /**
     * Pretty-prints a ProgramSV.
     *
     * @param pe the ProgramSV to be pretty-printed.
     */
    public void printProgramSV(ProgramSV pe) {
        printSourceElement(pe);
    }

    protected void printRewrite(Term t) {
        layouter.nl().beginC().print("\\replacewith(").brk(0);
        printTerm(t);
        layouter.brk(0, -2).print(")").end();
    }

    /**
     * Pretty-print a sequent. The sequent arrow is rendered as <code>=&gt;</code>. If the sequent
     * doesn't fit in one line, a line break is inserted after each formula, the sequent arrow is on
     * a line of its own, and formulae are indented w.r.t. the arrow. A line-break is printed after
     * the Sequent.
     *
     * @param filter The SequentPrintFilter for seq
     */
    public void printFilteredSequent(SequentPrintFilter filter) {
        try {
            ImmutableList<SequentPrintFilterEntry> antec = filter.getFilteredAntec();
            ImmutableList<SequentPrintFilterEntry> succ = filter.getFilteredSucc();

            layouter.markStartSub();
            layouter.startTerm(antec.size() + succ.size());

            layouter.beginC(1).ind();
            printSemisequent(antec);

            layouter.brk(1, -1);
            printSequentArrow();
            layouter.brk();

            printSemisequent(succ);

            layouter.markEndSub();
            layouter.end();
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException("Unbalanced blocks in pretty printer", e);
        }
    }

    private void printSequentInExistingBlock(Sequent seq) {
        try {
            Semisequent antec = seq.antecedent();
            Semisequent succ = seq.succedent();
            layouter.markStartSub();
            layouter.startTerm(antec.size() + succ.size());

            if (!antec.isEmpty()) {
                layouter.beginRelativeC(1);
                layouter.ind();
                printSemisequent(antec);
                layouter.end();
                layouter.brk();
            }

            printSequentArrow();
            if (!succ.isEmpty()) {
                layouter.beginRelativeC(1).brk();
                printSemisequent(succ);
                layouter.end();
            }

            layouter.markEndSub();
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException("Unbalanced blocks in pretty printer", e);
        }
    }

    /**
     * Pretty-print a sequent. The sequent arrow is rendered as <code>=&gt;</code>. If the sequent
     * doesn't fit in one line, a line break is inserted after each formula, the sequent arrow is on
     * a line of its own, and formulae are indented w.r.t. the arrow. A line-break is printed after
     * the Sequent. No filtering is done.
     *
     * @param seq The Sequent to be pretty-printed
     */
    public void printSequent(Sequent seq) {
        layouter.beginC(0);
        printSequentInExistingBlock(seq);
        layouter.end();
    }

    /**
     * Pretty-prints a Semisequent. Formulae are separated by commas.
     *
     * @param semiseq the semisequent to be printed
     */
    public void printSemisequent(Semisequent semiseq) {
        for (int i = 0; i < semiseq.size(); i++) {
            layouter.markStartSub();
            printConstrainedFormula(semiseq.get(i));
            layouter.markEndSub();
            if (i != semiseq.size() - 1) {
                layouter.print(",").brk();
            }
        }
    }

    public void printSemisequent(ImmutableList<SequentPrintFilterEntry> formulas) {
        Iterator<SequentPrintFilterEntry> it = formulas.iterator();
        SequentPrintFilterEntry entry;

        for (int size = formulas.size() - 1; size >= 0; --size) {
            entry = it.next();
            layouter.markStartSub();
            printConstrainedFormula(entry.getFilteredFormula());
            layouter.markEndSub();
            if (size != 0) {
                layouter.print(",").brk();
            }
        }
    }

    /**
     * Pretty-prints a constrained formula. The constraint "Constraint.BOTTOM" is suppressed
     *
     * @param cfma the constrained formula to be printed
     */
    public void printConstrainedFormula(SequentFormula cfma) {
        printTerm(cfma.formula());
    }

    /**
     * Pretty-prints a term or formula. How it is rendered depends on the NotationInfo given to the
     * constructor.
     *
     * @param t the Term to be printed
     */
    public void printTerm(Term t) {
        if (notationInfo.getAbbrevMap().isEnabled(t)) {
            layouter.startTerm(0);
            layouter.print(notationInfo.getAbbrevMap().getAbbrev(t));
        } else {
            if (t.hasLabels() && !getVisibleTermLabels(t).isEmpty() && notationInfo
                    .getNotation(t.op()).getPriority() < NotationInfo.PRIORITY_ATOM) {
                layouter.print("(");
            }
            notationInfo.getNotation(t.op()).print(t, this);
            if (t.hasLabels() && !getVisibleTermLabels(t).isEmpty() && notationInfo
                    .getNotation(t.op()).getPriority() < NotationInfo.PRIORITY_ATOM) {
                layouter.print(")");
            }
        }
        if (t.hasLabels()) {
            printLabels(t);
        }
    }

    /**
     * Determine the Set of labels that will be printed out for a specific {@link Term}. The class
     * {@link SequentViewLogicPrinter} overrides this method. {@link TermLabel} visibility can be
     * configured via GUI, see {@link de.uka.ilkd.key.gui.actions.TermLabelMenu}. Default is to
     * print all TermLabels.
     *
     * @param t {@link Term} whose visible {@link TermLabel}s will be determined.
     * @return List of visible {@link TermLabel}s, i.e. labels that are syntactically added to a
     *         {@link Term} while printing.
     */
    protected ImmutableArray<TermLabel> getVisibleTermLabels(Term t) {
        return t.getLabels();
    }

    public void printLabels(Term t) {
        notationInfo.getNotation(TermLabel.class).print(t, this);
    }

    void printLabels(Term t, String left, String right) {

        ImmutableArray<TermLabel> termLabelList = getVisibleTermLabels(t);
        if (termLabelList.isEmpty()) {
            return;
        }

        layouter.beginC().print(left);
        boolean afterFirst = false;

        for (TermLabel l : termLabelList) {
            if (afterFirst) {
                layouter.print(",").brk(1, 0);
            } else {
                afterFirst = true;
            }
            layouter.print(l.name().toString());
            if (l.getChildCount() > 0) {
                layouter.print("(").beginC();
                for (int i = 0; i < l.getChildCount(); i++) {
                    layouter.print("\"" + l.getChild(i).toString() + "\"");
                    if (i < l.getChildCount() - 1) {
                        layouter.print(",").ind(1, 2);
                    }
                }
                layouter.end().print(")");
            }
        }
        layouter.end().print(right);
    }

    /**
     * Pretty-prints a set of terms.
     *
     * @param terms the terms to be printed
     */
    public void printTerm(ImmutableSet<Term> terms) {
        layouter.print("{");
        Iterator<Term> it = terms.iterator();
        while (it.hasNext()) {
            printTerm(it.next());
            if (it.hasNext()) {
                layouter.print(", ");
            }
        }
        layouter.print("}");
    }

    /**
     * Pretty-prints a term or formula in the same block. How it is rendered depends on the
     * NotationInfo given to the constructor. `In the same block' means that no extra indentation
     * will be added if line breaks are necessary. A formula <code>a &amp; (b
     * &amp; c)</code> would print <code>a &amp; b &amp; c</code>, omitting the redundant
     * parentheses. The subformula <code>b &amp; c</code> is printed using this method to get a
     * layout of
     *
     * <pre>
     * a &amp; b &amp; c
     * </pre>
     * <p>
     * instead of
     *
     * <pre>
     * a &amp; b &amp; c
     * </pre>
     *
     * @param t the Term to be printed
     */
    public void printTermContinuingBlock(Term t) {
        if (t.hasLabels() && !getVisibleTermLabels(t).isEmpty()
                && notationInfo.getNotation(t.op()).getPriority() < NotationInfo.PRIORITY_ATOM) {
            layouter.print("(");
        }
        notationInfo.getNotation(t.op()).printContinuingBlock(t, this);
        if (t.hasLabels() && !getVisibleTermLabels(t).isEmpty()
                && notationInfo.getNotation(t.op()).getPriority() < NotationInfo.PRIORITY_ATOM) {
            layouter.print(")");
        }
        if (t.hasLabels()) {
            printLabels(t);
        }
    }

    /**
     * Print a term in <code>f(t1,...tn)</code> style. If the operator has arity 0, no parentheses
     * are printed, i.e. <code>f</code> instead of <code>f()</code>. If the term doesn't fit on one
     * line, <code>t2...tn</code> are aligned below <code>t1</code>.
     *
     * @param t the term to be printed.
     */
    public void printFunctionTerm(Term t) {
        boolean isKeyword = false;
        if (services != null) {
            Function measuredByEmpty = services.getTermBuilder().getMeasuredByEmpty();
            BooleanLDT bool = services.getTypeConverter().getBooleanLDT();
            IntegerLDT integer = services.getTypeConverter().getIntegerLDT();

            isKeyword = (t.op() == getHeapLDT().getWellFormed() || t.op() == measuredByEmpty
                    || t.op() == bool.getFalseConst() || t.op() == bool.getTrueConst()
                    || t.op() == integer.getBsum());
        }
        if (notationInfo.isPrettySyntax() && services != null
                && FieldPrinter.isJavaFieldConstant(t, getHeapLDT(), services)
                && getNotationInfo().isHidePackagePrefix()) {
            // Hide package prefix when printing field constants.
            layouter.startTerm(0);
            String name = t.op().name().toString();
            int index = name.lastIndexOf('.');
            String prettyFieldName = name.substring(index + 1);
            if (isKeyword) {
                layouter.markStartKeyword();
            }
            layouter.print(prettyFieldName);
            if (isKeyword) {
                layouter.markEndKeyword();
            }
        } else {
            String name = t.op().name().toString();
            layouter.startTerm(t.arity());
            boolean alreadyPrinted = false;
            if (t.op() instanceof SortDependingFunction) {
                SortDependingFunction op = (SortDependingFunction) t.op();
                if (op.getKind().compareTo(AbstractSort.EXACT_INSTANCE_NAME) == 0) {
                    layouter.print(op.getSortDependingOn().declarationString());
                    layouter.print("::");
                    layouter.keyWord(op.getKind().toString());
                    alreadyPrinted = true;
                }
            }
            if (isKeyword) {
                layouter.markStartKeyword();
            }
            if (!alreadyPrinted) {
                layouter.print(name);
            }
            if (isKeyword) {
                layouter.markEndKeyword();
            }
            if (!t.boundVars().isEmpty()) {
                layouter.print("{").beginC(0);
                printVariables(t.boundVars(), quantifiableVariablePrintMode);
                layouter.print("}").end();
            }
            if (t.arity() > 0) {
                layouter.print("(").beginC(0);
                for (int i = 0, n = t.arity(); i < n; i++) {
                    layouter.markStartSub();
                    printTerm(t.sub(i));
                    layouter.markEndSub();

                    if (i < n - 1) {
                        layouter.print(",").brk(1, 0);
                    }
                }
                layouter.print(")").end();
            }
        }
    }

    public void printCast(String pre, String post, Term t, int ass) {
        final SortDependingFunction cast = (SortDependingFunction) t.op();

        layouter.startTerm(t.arity());
        layouter.print(pre);
        layouter.print(cast.getSortDependingOn().toString());
        layouter.print(post);
        maybeParens(t.sub(0), ass);
    }

    protected boolean printEmbeddedHeapConstructorTerm(Term t) {

        Notation notation = notationInfo.getNotation(t.op());
        if (notation instanceof HeapConstructorNotation) {
            HeapConstructorNotation heapNotation = (HeapConstructorNotation) notation;
            heapNotation.printEmbeddedHeap(t, this);
            return true;
        } else {
            printTerm(t);
            return false;
        }
    }

    public void printClassName(String className) {
        layouter.print(className);
    }

    public void printHeapConstructor(Term t, boolean closingBrace) {
        assert t.boundVars().isEmpty();

        final HeapLDT heapLDT = getHeapLDT();

        if (notationInfo.isPrettySyntax() && heapLDT != null) {
            layouter.startTerm(t.arity());
            final Term heapTerm = t.sub(0);
            final String opName = t.op().name().toString();

            assert heapTerm.sort() == heapLDT.targetSort();

            layouter.markStartSub();
            boolean hasEmbedded = printEmbeddedHeapConstructorTerm(heapTerm);
            layouter.markEndSub();

            if (hasEmbedded) {
                layouter.brk(0);
            } else {
                layouter.beginC(0);
            }
            if (t.op() == getHeapLDT().getCreated()) {
                layouter.markStartKeyword();
            }
            layouter.print("[" + opName + "(").beginC(0);
            if (t.op() == getHeapLDT().getCreated()) {
                layouter.markEndKeyword();
            }
            for (int i = 1; i < t.arity(); i++) {
                // do not print anon_heap if parsability is not required
                if (getNotationInfo().isHidePackagePrefix() && "anon".equals(opName) && i == 2) {
                    break;
                }

                if (i > 1) {
                    layouter.print(",").brk(1, 0);
                }
                layouter.markStartSub();
                printTerm(t.sub(i));
                layouter.markEndSub();
            }

            layouter.print(")]").end();

            if (closingBrace) {
                layouter.end();
            }

        } else {
            printFunctionTerm(t);
        }
    }

    protected void printEmbeddedObserver(final Term heapTerm, final Term objectTerm) {
        Notation notation = notationInfo.getNotation(objectTerm.op());
        if (notation instanceof ObserverNotation) {
            ObserverNotation obsNotation = (ObserverNotation) notation;
            Term innerheap = objectTerm.sub(0);
            boolean paren = !heapTerm.equals(innerheap);
            if (paren) {
                layouter.print("(");
                obsNotation.printWithHeap(objectTerm, this, heapTerm);
                layouter.print(")");
            } else {
                obsNotation.printWithHeap(objectTerm, this, heapTerm);
            }
        } else {
            printTerm(objectTerm);
        }
    }

    /*
     * Print a term of the form: T::select(heap, object, field).
     */
    public void printSelect(Term t, Term tacitHeap) {
        selectPrinter.printSelect(this, t, tacitHeap);
    }

    /*
     * Print a term of the form: store(heap, object, field, value).
     */
    public void printStore(Term t, boolean closingBrace) {
        storePrinter.printStore(this, t, closingBrace);
    }

    /*
     * Print a term of the form: T::seqGet(Seq, int).
     */
    public void printSeqGet(Term t) {
        if (notationInfo.isPrettySyntax()) {
            layouter.startTerm(2);
            if (!t.sort().equals(Sort.ANY)) {
                layouter.print("(" + t.sort().toString() + ")");
            }
            layouter.markStartSub();
            printTerm(t.sub(0));
            layouter.markEndSub();

            layouter.print("[");
            layouter.markStartSub();
            printTerm(t.sub(1));
            layouter.markEndSub();
            layouter.print("]");
        } else {
            printFunctionTerm(t);
        }
    }

    public void printPostfix(Term t, String postfix) {
        if (notationInfo.isPrettySyntax()) {
            layouter.startTerm(t.arity());

            layouter.markStartSub();
            printTerm(t.sub(0));
            layouter.markEndSub();
            layouter.print(postfix);
        } else {
            printFunctionTerm(t);
        }
    }

    public void printObserver(Term t, Term tacitHeap) {
        assert t.op() instanceof IObserverFunction;
        assert t.boundVars().isEmpty();

        final HeapLDT heapLDT = getHeapLDT();

        final IObserverFunction obs = (IObserverFunction) t.op();

        boolean printFancy = false;

        if (notationInfo.isPrettySyntax() && heapLDT != null) {

            Sort heapSort = heapLDT.targetSort();
            int numHeaps = obs.getHeapCount(services);
            int stateCount = obs.getStateCount();
            int totalHeaps = stateCount * numHeaps;

            // TODO find a good way to pretty print / parse multiple-heap observers
            printFancy = totalHeaps == 1 && t.arity() >= 1 && t.sub(0).sort() == heapSort;
        }

        if (printFancy) {

            if (tacitHeap == null) {
                tacitHeap = services.getTermFactory().createTerm(heapLDT.getHeap());
            }

            // this needs not be 1 in general:
            int totalHeaps = 1;

            layouter.startTerm(obs.arity());

            layouter.beginC();

            if (!obs.isStatic()) {
                layouter.markStartSub(totalHeaps);
                printEmbeddedObserver(t.sub(0), t.sub(totalHeaps));
                layouter.markEndSub();
                layouter.print(".");
            }

            // Print class name if the field is static.
            String fieldName = obs.isStatic() ? HeapLDT.getClassName((Function) t.op()) + "." : "";
            fieldName += HeapLDT.getPrettyFieldName(t.op());
            boolean isKeyword = false;
            if (services != null) {
                isKeyword = (obs == services.getJavaInfo().getInv());
            }

            if (obs.getNumParams() > 0 || obs instanceof IProgramMethod) {
                JavaInfo javaInfo = services.getJavaInfo();
                if (t.arity() > 1) {
                    // in case arity > 1 we assume fieldName refers to a query (method call)
                    Term object = t.sub(1);
                    KeYJavaType keYJavaType = javaInfo.getKeYJavaType(object.sort());
                    String p;
                    try {
                        boolean canonical =
                            obs.isStatic() || ((obs instanceof IProgramMethod) && javaInfo
                                    .isCanonicalProgramMethod((IProgramMethod) obs, keYJavaType));
                        if (canonical) {
                            p = fieldName;
                        } else {
                            p = "(" + t.op() + ")";
                        }
                    } catch (NullPointerException e) {
                        // MU & MK: There are cases where this method fails.
                        // (e.g., if the receiver of the observer happens to be replaced by "null").
                        // better conservatively print empty String.
                        p = "";
                    }
                    layouter.print(p);
                } else {
                    // in case arity == 1 we assume fieldName refers to an array
                    layouter.print(fieldName);
                }

                layouter.print("(").beginC(0);
                int startIndex = totalHeaps + (obs.isStatic() ? 0 : 1);
                for (int i = startIndex; i < obs.arity(); i++) {
                    if (i != startIndex) {
                        layouter.print(",").brk(1, 0);
                    }
                    layouter.markStartSub(i);
                    printTerm(t.sub(i));
                    layouter.markEndSub();
                }
                layouter.print(")").end();
            } else {
                if (isKeyword) {
                    layouter.markStartKeyword();
                }
                layouter.print(fieldName);
                if (isKeyword) {
                    layouter.markEndKeyword();
                }
            }

            // must the heap be printed at all: no, if default heap.
            final Term heapTerm = t.sub(0);
            if (!heapTerm.equals(tacitHeap)) {
                layouter.brk(0).print("@");
                layouter.markStartSub(0);
                printTerm(heapTerm);
                layouter.markEndSub();
            } else {
                layouter.markStartSub(0);
                // heaps not printed
                layouter.markEndSub();
            }
            layouter.end();

        } else {
            printFunctionTerm(t);
        }
    }

    public void printSingleton(Term t) {
        assert t.arity() == 2;
        layouter.startTerm(2);
        layouter.print("{(").beginC(0);

        layouter.markStartSub();
        printTerm(t.sub(0));
        layouter.markEndSub();

        layouter.print(",").brk(1, 0);

        layouter.markStartSub();
        printTerm(t.sub(1));
        layouter.markEndSub();

        layouter.print(")}").end();
    }

    public void printSeqSingleton(Term t, String lDelimiter, String rDelimiter) {
        assert t.arity() == 1;
        layouter.startTerm(1);
        layouter.print(lDelimiter).beginC(0);
        layouter.markStartSub();
        printTerm(t.sub(0));
        layouter.markEndSub();
        layouter.print(rDelimiter).end();
    }

    public void printElementOf(Term t) {
        assert t.arity() == 3;
        layouter.startTerm(3);

        layouter.print("(").beginC(0);

        layouter.markStartSub();
        printTerm(t.sub(0));
        layouter.markEndSub();

        layouter.print(",").brk(1, 0);

        layouter.markStartSub();
        printTerm(t.sub(1));
        layouter.markEndSub();

        layouter.print(")").end();
        layouter.print(" ");
        layouter.keyWord("\\in");
        layouter.print(" ");

        layouter.markStartSub();
        printTerm(t.sub(2));
        layouter.markEndSub();
    }

    public void printElementOf(Term t, String symbol) {
        if (symbol == null) {
            printElementOf(t);
            return;
        }

        assert t.arity() == 3;
        layouter.startTerm(3);

        layouter.print("(").beginC(0);

        layouter.markStartSub();
        printTerm(t.sub(0));
        layouter.markEndSub();

        layouter.print(",").brk(1, 0);

        layouter.markStartSub();
        printTerm(t.sub(1));
        layouter.markEndSub();

        layouter.print(")").end();
        layouter.print(symbol);

        layouter.markStartSub();
        printTerm(t.sub(2));
        layouter.markEndSub();
    }

    /**
     * Print a unary term in prefix style. For instance <code>!a</code>. No line breaks are
     * possible.
     *
     * @param name the prefix operator
     * @param t whole term
     * @param sub the subterm to be printed
     * @param ass the associativity for the subterm
     */
    public void printPrefixTerm(String name, Term t, Term sub, int ass) {
        layouter.startTerm(1);
        if (t.op() == Junctor.NOT) {
            layouter.markStartKeyword();
        }
        layouter.print(name);
        if (t.op() == Junctor.NOT) {
            layouter.markEndKeyword();
        }
        maybeParens(sub, ass);
    }

    /**
     * Print a unary term in postfix style. For instance <code>t.a</code>, where <code>.a</code> is
     * the postfix operator. No line breaks are possible.
     *
     * @param name the postfix operator
     * @param t the subterm to be printed
     * @param ass the associativity for the subterm
     */
    public void printPostfixTerm(Term t, int ass, String name) {
        layouter.startTerm(1);
        maybeParens(t, ass);
        layouter.print(name);
    }

    /**
     * Print a binary term in infix style. For instance <code>p
     * &amp; q</code>, where <code>&amp;</code> is the infix operator. If line breaks are necessary,
     * the format is like
     *
     * <pre>
     * p & q
     * </pre>
     * <p>
     * The subterms are printed using {@link #printTermContinuingBlock(Term)}.
     *
     * @param l the left subterm
     * @param assLeft associativity for left subterm
     * @param name the infix operator
     * @param t whole term
     * @param r the right subterm
     * @param assRight associativity for right subterm
     */
    public void printInfixTerm(Term l, int assLeft, String name, Term t, Term r, int assRight) {
        int indent = name.length() + 1;
        layouter.beginC(indent);
        printInfixTermContinuingBlock(l, assLeft, name, t, r, assRight);
        layouter.end();
    }

    /**
     * Print a binary term in infix style, continuing a containing block. See
     * {@link #printTermContinuingBlock(Term)} for the idea. Otherwise, like
     * {@link #printInfixTerm(Term, int, String, Term, Term, int)}.
     *
     * @param l the left subterm
     * @param assLeft associativity for left subterm
     * @param name the infix operator
     * @param t whole term
     * @param r the right subterm
     * @param assRight associativity for right subterm
     */
    public void printInfixTermContinuingBlock(Term l, int assLeft, String name, Term t, Term r,
            int assRight) {
        boolean isKeyword = false;
        if (services != null) {
            LocSetLDT loc = services.getTypeConverter().getLocSetLDT();
            isKeyword = (t.op() == Junctor.AND || t.op() == Junctor.OR || t.op() == Junctor.IMP
                    || t.op() == Equality.EQV || t.op() == loc.getUnion());
        }
        int indent = name.length() + 1;
        layouter.startTerm(2);
        layouter.ind();
        maybeParens(l, assLeft);
        layouter.brk(1, -indent);
        if (isKeyword) {
            layouter.markStartKeyword();
        }
        layouter.print(name);
        if (isKeyword) {
            layouter.markEndKeyword();
        }
        layouter.ind(1, 0);
        maybeParens(r, assRight);
    }

    /**
     * Print a term with an update. This looks like <code>{u} t</code>. If line breaks are
     * necessary, the format is
     *
     * <pre>
     * {u}
     *   t
     * </pre>
     *
     * @param l the left brace
     * @param r the right brace
     * @param t the update term
     * @param ass3 associativity for phi
     */
    public void printUpdateApplicationTerm(String l, String r, Term t, int ass3) {
        assert t.op() instanceof UpdateApplication && t.arity() == 2;

        layouter.markStartUpdate();
        layouter.beginC().print(l);
        layouter.startTerm(t.arity());

        layouter.markStartSub();
        printTerm(t.sub(0));
        layouter.markEndSub();

        layouter.print(r);
        layouter.markEndUpdate();
        layouter.brk(0);

        maybeParens(t.sub(1), ass3);

        layouter.end();
    }

    /**
     * Print an elementary update. This looks like <code>loc := val</code>
     *
     * @param asgn the assignment operator (including spaces)
     * @param ass2 associativity for the new values
     */
    public void printElementaryUpdate(String asgn, Term t, int ass2) {
        ElementaryUpdate op = (ElementaryUpdate) t.op();

        assert t.arity() == 1;
        layouter.startTerm(1);

        layouter.print(op.lhs().name().toString());

        layouter.print(asgn);

        maybeParens(t.sub(0), ass2);
    }

    private void printParallelUpdateHelper(String separator, Term t, int ass) {
        assert t.arity() == 2;
        layouter.startTerm(2);

        if (t.sub(0).op() == UpdateJunctor.PARALLEL_UPDATE) {
            layouter.markStartSub();
            printParallelUpdateHelper(separator, t.sub(0), ass);
            layouter.markEndSub();
        } else {
            maybeParens(t.sub(0), ass);
        }

        layouter.brk().print(separator + " ");

        if (t.sub(1).op() == UpdateJunctor.PARALLEL_UPDATE) {
            layouter.markStartSub();
            layouter.print("(");
            printParallelUpdateHelper(separator, t.sub(1), ass);
            layouter.print(")");
            layouter.markEndSub();
        } else {
            maybeParens(t.sub(1), ass);
        }
    }

    public void printParallelUpdate(String separator, Term t, int ass) {
        layouter.beginC(0);
        printParallelUpdateHelper(separator, t, ass);
        layouter.end();
    }

    private void printVariables(ImmutableArray<QuantifiableVariable> vars,
            QuantifiableVariablePrintMode mode) {
        int size = vars.size();
        for (int j = 0; j != size; j++) {
            final QuantifiableVariable v = vars.get(j);
            if (v instanceof LogicVariable) {
                if (mode != QuantifiableVariablePrintMode.WITH_OUT_DECLARATION) {
                    // do not print declarations in taclets...
                    printClassName(v.sort().name().toString());
                    layouter.print(" ");
                }
                if (services != null && notationInfo.getAbbrevMap()
                        .containsTerm(services.getTermFactory().createTerm(v))) {
                    layouter.print(notationInfo.getAbbrevMap()
                            .getAbbrev(services.getTermFactory().createTerm(v)));
                } else {
                    layouter.print(v.name().toString());
                }
            } else {
                layouter.print(v.name().toString());
            }
            if (j < size - 1) {
                layouter.print(", ");
            }
        }
        layouter.print(";");
    }

    public void printIfThenElseTerm(Term t, String keyword) {
        layouter.startTerm(t.arity());

        layouter.beginC(0);
        layouter.keyWord(keyword);
        if (t.varsBoundHere(0).size() > 0) {
            layouter.print(" ");
            printVariables(t.varsBoundHere(0), quantifiableVariablePrintMode);
        }

        layouter.print(" (");
        layouter.markStartSub();
        printTerm(t.sub(0));
        layouter.markEndSub();
        layouter.print(")");

        for (int i = 1; i < t.arity(); ++i) {
            layouter.brk(1, 3);
            layouter.print(" ");
            layouter.markStartKeyword();
            if (i == 1) {
                layouter.print("\\then");
            } else {
                layouter.print("\\else");
            }
            layouter.markEndKeyword();
            layouter.print(" (");
            layouter.markStartSub();
            printTerm(t.sub(i));
            layouter.markEndSub();
            layouter.print(")");
        }

        layouter.end();
    }

    /**
     * Print a substitution term. This looks like <code>{var/t}s</code>. If line breaks are
     * necessary, the format is
     *
     * <pre>
     * {var/t}
     *   s
     * </pre>
     *
     * @param l the String used as left brace symbol
     * @param v the {@link QuantifiableVariable} to be substituted
     * @param t the Term to be used as new value
     * @param ass2 the int defining the associativity for the new value
     * @param r the String used as right brace symbol
     * @param phi the substituted term/formula
     * @param ass3 the int defining the associativity for phi
     */
    public void printSubstTerm(String l, QuantifiableVariable v, Term t, int ass2, String r,
            Term phi, int ass3) {
        layouter.beginC().print(l);
        printVariables(new ImmutableArray<>(v), quantifiableVariablePrintMode);
        layouter.startTerm(2);
        maybeParens(t, ass2);
        layouter.print(r).brk(0);
        maybeParens(phi, ass3);
        layouter.end();
    }

    /**
     * Print a quantified term. Normally, this looks like <code>all x:s.phi</code>. If line breaks
     * are necessary, the format is
     *
     * <pre>
     * all x:s.
     *   phi
     * </pre>
     * <p>
     * Note that the parameter <code>var</code> has to contain the variable name with colon and
     * sort.
     *
     * @param name the name of the quantifier
     * @param vars the quantified variables (+colon and sort)
     * @param phi the quantified formula
     * @param ass associativity for phi
     */
    public void printQuantifierTerm(String name, ImmutableArray<QuantifiableVariable> vars,
            Term phi, int ass) {
        layouter.beginC();
        layouter.keyWord(name);
        layouter.print(" ");
        printVariables(vars, quantifiableVariablePrintMode);
        layouter.brk();
        layouter.startTerm(1);
        maybeParens(phi, ass);
        layouter.end();
    }

    /**
     * Print a constant. This just prints the string <code>s</code> and marks it as a nullary term.
     *
     * @param s the constant
     */
    public void printConstant(String s) {
        layouter.startTerm(0);
        layouter.print(s);
    }

    /**
     * Print a constant. This just prints the string <code>s</code> and marks it as a nullary term.
     *
     * @param t constant as term to be printed
     * @param s name of the constant
     */
    public void printConstant(Term t, String s) {
        layouter.startTerm(0);
        boolean isKeyword = false;
        if (getHeapLDT() != null) {
            isKeyword = (t.op() == Junctor.FALSE || t.op() == Junctor.TRUE
                    || t.op() == getHeapLDT().getCreated());
        }
        if (isKeyword) {
            layouter.markStartKeyword();
        }
        layouter.print(s);
        if (isKeyword) {
            layouter.markEndKeyword();
        }
    }

    /**
     * Print a Java block. This is formatted using the ProgramPrinter given to the constructor. The
     * result is indented according to the surrounding material. The first `executable' statement is
     * marked for highlighting.
     *
     * @param j the Java block to be printed
     */
    public void printJavaBlock(JavaBlock j) {
        printSourceElement(j.program());
    }

    /**
     * Print a DL modality formula. <code>phi</code> is the whole modality formula, not just the
     * subformula inside the modality. Normally, this looks like <code>&lt;Program&gt;psi</code>,
     * where <code>psi = phi.sub(0)</code>. No line breaks are inserted, as the program itself is
     * always broken. In case of a program modality with arity greater than 1, the subformulae are
     * listed between parens, like <code>&lt;Program&gt;(psi1,psi2)</code>
     */

    public void printModalityTerm(String left, JavaBlock jb, String right, Term phi, int ass) {
        assert jb != null;
        assert jb.program() != null;
        if (phi.op() instanceof ModalOperatorSV) {
            Object o = getInstantiations().getInstantiation((ModalOperatorSV) phi.op());
            if (o != null) {
                if (notationInfo.getAbbrevMap().isEnabled(phi)) {
                    layouter.startTerm(0);
                    layouter.print(notationInfo.getAbbrevMap().getAbbrev(phi));
                } else {
                    Term[] ta = new Term[phi.arity()];
                    for (int i = 0; i < phi.arity(); i++) {
                        ta[i] = phi.sub(i);
                    }
                    Term term = services.getTermFactory().createTerm((Modality) o, ta,
                        phi.boundVars(), phi.javaBlock());
                    notationInfo.getNotation((Modality) o).print(term, this);
                    return;
                }

            }
        }

        layouter.markModPosTbl();
        layouter.startTerm(phi.arity());
        layouter.print(left);
        layouter.markStartJavaBlock();
        printJavaBlock(jb);
        layouter.markEndJavaBlock();
        layouter.print(right + " ");
        if (phi.arity() == 1) {
            maybeParens(phi.sub(0), ass);
        } else if (phi.arity() > 1) {
            layouter.print("(");
            for (int i = 0; i < phi.arity(); i++) {
                layouter.markStartSub();
                printTerm(phi.sub(i));
                layouter.markEndSub();
                if (i < phi.arity() - 1) {
                    layouter.print(",").brk(1, 0);
                }
            }
            layouter.print(")");
        }
    }

    /**
     * Returns the pretty-printed sequent in a StringBuffer. This should only be called after a
     * <tt>printSequent</tt> invocation returns.
     *
     * @return the pretty-printed sequent.
     */
    public String result() {
        return layouter.result();
    }

    /**
     * Prints a subterm, if needed with parentheses. Each subterm has a Priority. If the priority is
     * less than the associativity for that subterm fixed by the Notation/NotationInfo, parentheses
     * are needed.
     *
     * <p>
     * If prio and associativity are equal, the subterm is printed using
     * {@link #printTermContinuingBlock(Term)}. This currently only makes a difference for infix
     * operators.
     *
     * @param t the subterm to print
     * @param ass the associativity for this subterm
     */
    protected void maybeParens(Term t, int ass) {
        if (t.op() instanceof SchemaVariable && instantiations != null
                && instantiations.getInstantiation((SchemaVariable) t.op()) instanceof Term) {
            t = (Term) instantiations.getInstantiation((SchemaVariable) t.op());
        }

        if (notationInfo.getNotation(t.op()).getPriority() < ass) {
            layouter.markStartSub();
            layouter.print("(");
            printTerm(t);
            layouter.print(")");
            layouter.markEndSub();
        } else {
            layouter.markStartSub();
            if (notationInfo.getNotation(t.op()).getPriority() == ass) {
                printTermContinuingBlock(t);
            } else {
                printTerm(t);
            }
            layouter.markEndSub();
        }
    }

    protected void printSequentArrow() {
        if (getNotationInfo().isUnicodeEnabled()) {
            layouter.print(Character.toString(UnicodeHelper.SEQUENT_ARROW));
        } else {
            layouter.print("==>");
        }
    }

    /**
     * @return The SVInstantiations given with the last printTaclet call.
     */
    public SVInstantiations getInstantiations() {
        return instantiations;
    }

    /**
     * returns true if an attribute term shall be printed in short form. In opposite to the other
     * <tt>printInShortForm</tt> methods it takes care of meta variable instantiations
     *
     * @param attributeProgramName the String of the attribute's program name
     * @param t the Term used as reference prefix
     * @return true if an attribute term shall be printed in short form.
     */
    public boolean printInShortForm(String attributeProgramName, Term t) {
        final Sort prefixSort;
        prefixSort = t.sort();
        return printInShortForm(attributeProgramName, prefixSort);
    }

    /**
     * tests if the program name together with the prefix sort determines the attribute in a unique
     * way
     *
     * @param programName the String denoting the program name of the attribute
     * @param sort the ObjectSort in whose reachable hierarchy we test for uniqueness
     * @return true if the attribute is uniquely determined
     */
    public boolean printInShortForm(String programName, Sort sort) {
        return printInShortForm(programName, sort, services);
    }

    /**
     * escapes special characters by their HTML encoding
     *
     * @param text the String to be displayed as part of an HTML side
     * @return the text with special characters replaced
     */
    public static String escapeHTML(String text, boolean escapeWhitespace) {
        StringBuilder sb = new StringBuilder();

        for (int i = 0, sz = text.length(); i < sz; i++) {
            char c = text.charAt(i);
            switch (c) {
            case '<':
                sb.append("&lt;");
                break;
            case '>':
                sb.append("&gt;");
                break;
            case '&':
                sb.append("&amp;");
                break;
            case '\"':
                sb.append("&quot;");
                break;
            case '\'':
                sb.append("&#039;");
                break;
            case '(':
                sb.append("&#040;");
                break;
            case ')':
                sb.append("&#041;");
                break;
            case '#':
                sb.append("&#035;");
                break;
            case '+':
                sb.append("&#043;");
                break;
            case '-':
                sb.append("&#045;");
                break;
            case '%':
                sb.append("&#037;");
                break;
            case ';':
                sb.append("&#059;");
                break;
            case '\n':
                sb.append(escapeWhitespace ? "<br>" : c);
                break;
            case ' ':
                sb.append(escapeWhitespace ? "&nbsp;" : c);
                break;
            default:
                sb.append(c);
            }

        }
        return sb.toString();
    }

    /**
     * tests if the program name together with the prefix sort determines the attribute in a unique
     * way
     *
     * @param programName the String denoting the program name of the attribute
     * @param sort the ObjectSort specifying the hierarchy where to test for uniqueness
     * @param services the Services class used to access the type hierarchy
     * @return true if the attribute is uniquely determined
     */
    public static boolean printInShortForm(String programName, Sort sort, Services services) {
        if (!(services != null && sort.extendsTrans(services.getJavaInfo().objectSort()))) {
            return false;
        }
        final KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
        assert kjt != null : "Did not find KeYJavaType for " + sort;
        return services.getJavaInfo().getAllAttributes(programName, kjt).size() == 1;
    }
}
