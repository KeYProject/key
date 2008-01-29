// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;

import java.io.IOException;
import java.io.StringWriter;
import java.util.*;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.op.oclop.OclOp;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.pp.Backend;
import de.uka.ilkd.key.util.pp.Layouter;
import de.uka.ilkd.key.util.pp.StringBackend;
import de.uka.ilkd.key.util.pp.UnbalancedBlocksException;


/**
 * The front end for the Sequent pretty-printer.  It prints a sequent
 * and its parts and computes the PositionTable, which is needed for
 * highliting.
 *
 * <P>The actual layouting/formatting is done using the {@link
 * de.uka.ilkd.key.util.pp.Layouter} class.  The concrete syntax for
 * operators is given by an instance of {@link NotationInfo}.  The
 * LogicPrinter is responsible for the concrete <em>layout</em>,
 * e.g. how terms with infix operators are indented, and it binds the
 * various needed components together.
 *
 * @see NotationInfo
 * @see Notation
 * @see de.uka.ilkd.key.util.pp.Layouter
 *
 *
 */
public class LogicPrinter {

    /**
     * The default and minimal value o fthe
     * max. number of characters to put in one line
     */
    public static final int DEFAULT_LINE_WIDTH = 55;

    /** The max. number of characters to put in one line */
    protected int lineWidth = DEFAULT_LINE_WIDTH;

    /**
     * The ProgramPrinter used to pretty-print Java blocks in
     * formulae.
     */
    protected ProgramPrinter prgPrinter;

    /** Contains information on the concrete syntax of operators. */
    private final NotationInfo notationInfo;

    /** the services object */
    protected final Services services;

    /** The sequent we are pretty-printing */
    //private Sequent            seq;
    //private SequentPrintFilter filter;

    /** This chooses the layout. */
    protected Layouter layouter;

    /** The backend <code>layouter</code> will write to. */
    protected Backend backend;

    /** The constraint used for metavariable instantiations of the
     * current formula */
    Constraint formulaConstraint = null;

    /**If pure is true the PositionTable will not be calculated */
    private boolean pure = false;

    protected SVInstantiations instantiations = 
        SVInstantiations.EMPTY_SVINSTANTIATIONS;

    /** For OCL Simplification. So that OCL/UML properties
        are pretty-printed the right way. */
    private boolean oclPrettyPrinting = false;

    protected static Logger logger = Logger.getLogger(LogicPrinter.class.getName());


    public static String quickPrintLocationDescriptors(
                                        SetOfLocationDescriptor locations,
                                        Services services) {
        
        final NotationInfo ni = NotationInfo.createInstance();
        if (services != null) {
            PresentationFeatures.modifyNotationInfo(ni,
                    services.getNamespaces().functions());
        }
        LogicPrinter p = new LogicPrinter(null, 
        				  ni, 
        				  services);
        try {
            p.printLocationDescriptors(locations);
        } catch (IOException ioe) {
            return locations.toString();
        }
        return p.result().toString();
    }
    
    
    public static String quickPrintTerm(Term t, Services services) {
        final NotationInfo ni = NotationInfo.createInstance();
        if (services != null) {
            PresentationFeatures.modifyNotationInfo(ni,
                    services.getNamespaces().functions());
        }
        LogicPrinter p = new LogicPrinter(null, 
                                          ni, 
                                          services);
        try {
            p.printTerm(t);
        } catch (IOException ioe) {
            return t.toString();
        }
        return p.result().toString();
    }
    

    /**
     * Creates a LogicPrinter.  Sets the sequent to be printed, as
     * well as a ProgramPrinter to print Java programs and a
     * NotationInfo which determines the concrete syntax.
     *
     * @param prgPrinter   the ProgramPrinter that pretty-prints Java programs
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param services     The Services object
     */
    public LogicPrinter(ProgramPrinter prgPrinter,
                        NotationInfo notationInfo,
                        Services services) {
	backend           = new PosTableStringBackend(lineWidth);
	layouter          = new Layouter(backend,2);
	this.prgPrinter   = prgPrinter;
	this.notationInfo = notationInfo;
	this.services     = services;
    }

    /**
     * Creates a LogicPrinter.  Sets the sequent to be printed, as
     * well as a ProgramPrinter to print Java programs and a
     * NotationInfo which determines the concrete syntax.
     *
     * @param prgPrinter   the ProgramPrinter that pretty-prints Java programs
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param backend      the Backend for the output
     * @param services     the Services object
     */

    public LogicPrinter(ProgramPrinter prgPrinter,
                        NotationInfo notationInfo,
                        Backend backend,
                        Services services) {
	this.backend      = backend;
	layouter          = new Layouter(backend,2);
	this.prgPrinter   = prgPrinter;
	this.notationInfo = notationInfo;
	this.services     = services;
    }

    /**
     * Creates a LogicPrinter.  Sets the sequent to be printed, as
     * well as a ProgramPrinter to print Java programs and a
     * NotationInfo which determines the concrete syntax.
     *
     * @param prgPrinter   the ProgramPrinter that pretty-prints Java programs
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param purePrint    if true the PositionTable will not be calculated
     *               (simulates the behaviour of the former PureSequentPrinter)
     * @param services     the Services object               
     */
    public LogicPrinter(ProgramPrinter prgPrinter,
                        NotationInfo notationInfo, 
                        Services services,
                        boolean purePrint) {
        backend           = new PosTableStringBackend(lineWidth);
        layouter          = new Layouter(backend,2);
        this.prgPrinter   = prgPrinter;
        this.notationInfo = notationInfo;
        this.services     = services;
        pure = purePrint;
    }

    /**
     * Creates a LogicPrinter.  Sets the sequent to be printed, as
     * well as a ProgramPrinter to print Java programs and a
     * NotationInfo which determines the concrete syntax.
     *
     * @param prgPrinter   the ProgramPrinter that pretty-prints Java programs
     * @param notationInfo the NotationInfo for the concrete syntax
     * @param backend      the Backend for the output
     * @param purePrint    if true the PositionTable will not be calculated
                    (simulates the behaviour of the former PureSequentPrinter)
     */
    public LogicPrinter(ProgramPrinter prgPrinter,
                        NotationInfo notationInfo,
                        Backend backend, 
                        Services services,
                        boolean purePrint) {
        this.backend      = backend;
        layouter          = new Layouter(backend,2);
        this.prgPrinter   = prgPrinter;
        this.notationInfo = notationInfo;
        this.services     = services;
        pure = purePrint;
    }


    /**
     * @return the notationInfo associated with this LogicPrinter
     */
    public NotationInfo getNotationInfo(){
        return notationInfo;
    }
    /**
     * Resets the Backend, the Layouter and (if applicable) the ProgramPrinter
     * of this Object.
     */
    public void reset() {
        backend = new PosTableStringBackend(lineWidth);
        layouter = new Layouter(backend,2);
        if (prgPrinter != null) {
            prgPrinter.reset();
        }
    }

    /**
     * sets the line width to the new value but does <em>not</em>
     *  reprint the sequent.
     * The actual set line width is the maximum of
     *   {@link LogicPrinter#DEFAULT_LINE_WIDTH} and the given value
     * @param lineWidth the max. number of character to put on one line
     * @return the actual set line width
     */
    public int setLineWidth(int lineWidth) {
        this.lineWidth = lineWidth<DEFAULT_LINE_WIDTH ?
                DEFAULT_LINE_WIDTH : lineWidth;
        return this.lineWidth;
    }


    /** Reprints the sequent.  This can be useful if settings like
     * PresentationFeatures or abbreviations have changed.
     * @param seq The Sequent to be reprinted
     * @param filter The SequentPrintFilter for seq
     * @param lineWidth the max. number of character to put on one line
     *   (the actual taken linewidth is the max of
     *   {@link LogicPrinter#DEFAULT_LINE_WIDTH} and the given value
     */
    public void update(Sequent seq, SequentPrintFilter filter,
            int lineWidth) {
        setLineWidth(lineWidth);
        reset();
        printSequent(seq, filter);
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
         * @param taclet
         *           The Taclet to be pretty-printed.
         * @param sv
         *           The instantiations of the SchemaVariables
         * @param showWholeTaclet
         *           Should the find, varcond and heuristic part be pretty-printed?
         */
    public void printTaclet(Taclet taclet, SVInstantiations sv,
                            boolean showWholeTaclet) {
	instantiations = sv;
	try {
	    if (logger.isDebugEnabled()) {
		logger.debug(taclet.name().toString());
	    }
	    if (showWholeTaclet) {
		layouter.beginC(2).print(taclet.name().toString()).print(" {");
	    } else {
		layouter.beginC();
	    }
	    if (!(taclet.ifSequent().isEmpty())) {
		printTextSequent(taclet.ifSequent(), "\\assumes", true);
	    }
	    if (showWholeTaclet) {
		printFind(taclet);
		if (taclet instanceof RewriteTaclet) {
		    printRewriteAttributes((RewriteTaclet)taclet);
		}
		printVarCond(taclet);
	    }
	    printGoalTemplates(taclet);
	    if (showWholeTaclet) {
		printHeuristics(taclet);
	    }
	    printAttribs(taclet);
	    if (showWholeTaclet) {
		layouter.brk(1, -2).print("}");
	    }
	    layouter.end();
	} catch (java.io.IOException e) {
	    logger.warn("xxx exception occurred during printTaclet");
	}
	instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
    }

    /**
     * Pretty-print a taclet. Line-breaks are taken care of. No instantiation is
     * applied.
     *
     * @param taclet
     *           The Taclet to be pretty-printed.
     */
    public void printTaclet(Taclet taclet) {
        printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
    }

    protected void printAttribs(Taclet taclet) throws IOException{
        if (taclet.noninteractive()) {
                layouter.brk().print("\\noninteractive");
        }       
    }

    protected void printRewriteAttributes(RewriteTaclet taclet) throws IOException{
        final int stateRestriction = taclet.getStateRestriction();
        if (stateRestriction == RewriteTaclet.SAME_UPDATE_LEVEL) {
            layouter.brk().print("\\sameUpdateLevel");
        } else if (stateRestriction == RewriteTaclet.IN_SEQUENT_STATE) {
            layouter.brk().print("\\inSequentState");
        }
    }

    protected void printVarCond(Taclet taclet) throws IOException{
        IteratorOfNewVarcond itVarsNew      = taclet.varsNew().iterator();
        IteratorOfNewDependingOn itVarsNewDepOn = taclet.varsNewDependingOn();
        IteratorOfNotFreeIn itVarsNotFreeIn = taclet.varsNotFreeIn();
        IteratorOfVariableCondition itVC = taclet.getVariableConditions();

        if (itVarsNew.hasNext() ||
                itVarsNotFreeIn.hasNext() ||
                itVC.hasNext() || itVarsNewDepOn.hasNext()) {
            layouter.brk().beginC(2).print("\\varcond (").brk();
            while (itVarsNewDepOn.hasNext()) {
                printNewVarDepOnCond(itVarsNewDepOn.next());
                if (itVarsNewDepOn.hasNext() || 
                        itVarsNew.hasNext() || 
                        itVarsNotFreeIn.hasNext() || 
                        itVC.hasNext()) {
                        layouter.print(",").brk(); 
                }
            }
            while (itVarsNew.hasNext()) {
            	printNewVarcond(itVarsNew.next());
            	if (itVarsNew.hasNext() || itVarsNotFreeIn.hasNext() 
		    || itVC.hasNext()) {
            		layouter.print(",").brk(); 
            	}
            }
            while (itVarsNotFreeIn.hasNext()) {
                NotFreeIn pair=itVarsNotFreeIn.next();
                printNotFreeIn(pair);
                if (itVarsNotFreeIn.hasNext() || itVC.hasNext()) {
                        layouter.print(",").brk();
                }
            }
            while (itVC.hasNext()) {
                printVariableCondition(itVC.next());
                if (itVC.hasNext()){
                        layouter.print(",").brk();
                }
            }
            layouter.brk(1,-2).print(")").end();
        }
    }
    
    private void printNewVarDepOnCond(NewDependingOn on) throws IOException {
        layouter.beginC(0);
        layouter.brk().print("\\new( ");
        printSchemaVariable(on.first());
        layouter.print(",").brk();
        layouter.print("\\dependingOn(");
        printSchemaVariable(on.second());
        layouter.brk(0,-2).print(")").brk();
        layouter.brk(0,-2).print(")").end();
    }

    protected void printNewVarcond(NewVarcond sv) throws IOException {
        layouter.beginC(0);
        layouter.brk().print("\\new(");
        printSchemaVariable(sv.getSchemaVariable());
        layouter.print(",").brk();
        if (sv.isDefinedByType()) {
            layouter.print(sv.getSort().toString());
        } else {
            if (sv.isDefinedByElementSort()) {
                layouter.print("\\elemTypeof (").brk();
            } else {
                layouter.print("\\typeof (").brk();
            }
            printSchemaVariable(sv.getPeerSchemaVariable());
            layouter.brk(0,-2).print(")").brk();
        }
        layouter.brk(0,-2).print(")").end();
    }

    protected void printNotFreeIn(NotFreeIn sv) throws IOException {
    	layouter.beginI(0);
    	layouter.brk().print("\\notFreeIn(").brk();
    	printSchemaVariable(sv.first());
    	layouter.print(",").brk();
    	printSchemaVariable(sv.second());
    	layouter.brk(0,-2).print(")").end();
    }

    protected void printVariableCondition(VariableCondition sv) throws IOException {
        layouter.print(sv.toString());
    }

    protected void printHeuristics(Taclet taclet) throws IOException{
        if (taclet.getRuleSets().size() == 0) {
                return;
        }
                layouter.brk().beginC(2).print("\\heuristics (");
                for (IteratorOfRuleSet it = taclet.getRuleSets().iterator(); it.hasNext();) {
                        layouter.brk();
                        RuleSet tgt = it.next();
                        printHeuristic(tgt);
                        if (it.hasNext()) {
                                layouter.print(",");
                        }
                }
                layouter.brk(1,-2).print(")").end();
    }

    protected void printHeuristic(RuleSet sv) throws IOException {
	layouter.print(sv.name().toString());
    }
    

    protected void printFind(Taclet taclet) throws IOException{
                if (!(taclet instanceof FindTaclet)) {
                    return;
                }
                layouter.brk().beginC(2).print("\\find (").brk();
                if (taclet instanceof SuccTaclet) {
                    layouter.print("==>").brk();
                }
                printTerm(((FindTaclet)taclet).find());
                if (taclet instanceof AntecTaclet) {
                    layouter.brk().print("==>");
                }
                layouter.brk(1,-2).print(")").end();
    }

    protected void printTextSequent(Sequent seq,
                                    String text,
                                    boolean frontbreak) throws IOException{

                if (frontbreak) {
                    layouter.brk();
                }

                layouter.beginC(2).print(text).print(" (");
                printSequent(seq, null, false);
                layouter.brk(1,-2).print(")").end();
    }

    protected void printGoalTemplates(Taclet taclet) throws IOException{
        //layouter.beginC(0);
        if (taclet.closeGoal()) {
            layouter.brk().print("\\closegoal").brk();
        }

        for (final IteratorOfTacletGoalTemplate it =
                 taclet.goalTemplates().reverse().iterator(); it.hasNext();) {
            printGoalTemplate(it.next());
            if (it.hasNext()) {
                layouter.print(";");
            }
        }
        //layouter.end();
    }

    protected void printGoalTemplate(TacletGoalTemplate tgt) throws IOException{
	//layouter.beginC(0);
	if (tgt.name() != null) {
	    if (tgt.name().length() > 0) {
		layouter.brk().beginC(2).print(tgt.name()).print(" {");
	    }
			
	}
	if (!(tgt.sequent().isEmpty())) {
	    printTextSequent(tgt.sequent(), "\\add", true);
	} 
	if (tgt.rules()!=SLListOfTaclet.EMPTY_LIST) {
	    printRules(tgt.rules());
	}
	if (tgt.addedProgVars().size()>0) {
	    layouter.brk();
	    printAddProgVars(tgt.addedProgVars());
	}
	
	if (tgt instanceof AntecSuccTacletGoalTemplate) {
	    printTextSequent
		(((AntecSuccTacletGoalTemplate)tgt).replaceWith(), 
		 "\\replacewith", true);
	}
	if (tgt instanceof RewriteTacletGoalTemplate) {
	    layouter.brk();
	    printRewrite(((RewriteTacletGoalTemplate)tgt).replaceWith());
	}
	if (tgt.name() != null) {
	    if (tgt.name().length() > 0) {
		layouter.brk(1,-2).print("}").end();
	    }
	}
	//layouter.end();
    }

    protected void printRules (ListOfTaclet rules) throws IOException{
        layouter.brk().beginC(2).print("\\addrules (");
        SVInstantiations svi = instantiations;
        for (IteratorOfTaclet it = rules.iterator(); it.hasNext();) {
            layouter.brk();
            Taclet t = it.next();
            printTaclet(t, instantiations, true);
            instantiations = svi;
        }
        layouter.brk(1,-2).print(")").end();
    }

    protected void printAddProgVars(SetOfSchemaVariable apv) throws IOException {
        layouter.beginC(2).print("\\addprogvars (");
        for (IteratorOfSchemaVariable it = apv.iterator(); it.hasNext();) {
            layouter.brk();
            SchemaVariable tgt = it.next();
            printSchemaVariable(tgt);
            if (it.hasNext()) {
                layouter.print(",");
            }
        }
        layouter.brk(1,-2).print(")").end();
    }

    protected void printSchemaVariable(SchemaVariable sv) throws IOException {
	Object o = getInstantiations().getInstantiation(sv);
	if (o == null) {
	    if (sv.isProgramSV()) {
		Debug.assertTrue(sv instanceof SortedSchemaVariable);
		printProgramSV((ProgramSV)sv);
	    } else {
		printConstant(sv.name().toString());
	    }
	} else {
	    if (o instanceof Term) {
		printTerm((Term)o);
	    } else if (o instanceof ProgramElement) {
		printProgramElement((ProgramElement)o);
	    } else {		
		logger.warn("Unknown instantiation type of " + o + 
			    "; class is " + o.getClass().getName());
		printConstant(sv.name().toString());
	    }
	}
    }

    /**
     * Pretty-prints a ProgramElement.
     *
     * @param pe
     *           You've guessed it, the ProgramElement to be pretty-printed
     * @throws IOException
     */
    public void printProgramElement(ProgramElement pe) throws IOException {
        if (pe instanceof ProgramVariable) {
            printProgramVariable((ProgramVariable) pe);
        } else {
            StringWriter w = new StringWriter();
            PrettyPrinter pp = new PrettyPrinter(w, true, instantiations);
            pe.prettyPrint(pp);
            layouter.pre(w.toString());
        }
    }

    /**
     * Pretty-Prints a ProgramVariable in the logic, not in Java blocks. Prints
     * out the full (logic) name, so if A.b is private, it becomes a.A::b .
     *
     * @param pv
     *           The ProgramVariable in the logic
     * @throws IOException
     */
    public void printProgramVariable(ProgramVariable pv) throws IOException {
        if (logger.isDebugEnabled()) {
            logger.debug("PP PV " + pv.name());
        }
        layouter.beginC().print(pv.name().toString()).end();
    }

    /**
     * Pretty-prints a ProgramSV.
     *
     * @param pe
     *           You've guessed it, the ProgramSV to be pretty-printed
     * @throws IOException
     */
    public void printProgramSV(ProgramSV pe)
        throws IOException {
        StringWriter w = new StringWriter();
        PrettyPrinter pp = new PrettyPrinter(w, true, instantiations);
        pe.prettyPrint(pp);
        layouter.pre(w.toString());
    }

    protected void printRewrite(Term t) throws IOException {
        layouter.beginC(2).print("\\replacewith (").brk();
        printTerm(t);
        layouter.brk(1,-2).print(")").end();
    }


    /**
     * Pretty-print a sequent.
     * The sequent arrow is rendered as <code>==&gt;</code>.  If the
     * sequent doesn't fit in one line, a line break is inserted after each
     * formula, the sequent arrow is on a line of its own, and formulae
     * are indented w.r.t. the arrow.
     * @param seq The Sequent to be pretty-printed
     * @param filter The SequentPrintFilter for seq
     * @param finalbreak Print an additional line-break at the end of the sequent.
     */
    public void printSequent(Sequent seq,
                             SequentPrintFilter filter,
                             boolean finalbreak) {
        if ( seq != null ) {
            printSequent(seq,finalbreak);
        } else if ( filter != null ) {
            printSequent(filter,finalbreak);
        }
    }

    public void printSequent(SequentPrintFilter filter,
                             boolean finalbreak) {
        try {
            ListOfSequentPrintFilterEntry antec = filter.getAntec();
            ListOfSequentPrintFilterEntry succ  = filter.getSucc();
            markStartSub();
            startTerm(antec.size()+succ.size());
            layouter.beginC(1).ind();
            printSemisequent(antec);
            layouter.brk(1,-1).print("==>").brk(1);
            printSemisequent(succ);
            if (finalbreak) {
                layouter.brk(0);
            }
            markEndSub();
            layouter.end();
        } catch (IOException e) {
            throw new RuntimeException (
                                        "IO Exception in pretty printer:\n"+e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException (
                                        "Unbalanced blocks in pretty printer:\n"+e);
        }
    }

    public void printSequent(Sequent seq,
                             boolean finalbreak) {
        try {
            Semisequent antec = seq.antecedent();
            Semisequent succ  = seq.succedent();
            markStartSub();
            startTerm(antec.size()+succ.size());
            layouter.beginC(1).ind();
            printSemisequent(antec);
            layouter.brk(1,-1).print("==>").brk(1);
            printSemisequent(succ);
            if (finalbreak) {
                layouter.brk(0);
            }
            markEndSub();
            layouter.end();
        } catch (IOException e) {
            throw new RuntimeException ("IO Exception in pretty printer:\n"+e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException (
                                        "Unbalanced blocks in pretty printer:\n"+e);
        }
    }


    /**
     * Pretty-print a sequent.
     * The sequent arrow is rendered as <code>=&gt;</code>.  If the
     * sequent doesn't fit in one line, a line break is inserted after each
     * formula, the sequent arrow is on a line of its own, and formulae
     * are indented w.r.t. the arrow.
     * A line-break is printed after the Sequent.
     * @param seq The Sequent to be pretty-printed
     * @param filter The SequentPrintFilter for seq
     */
    public void printSequent(Sequent seq, SequentPrintFilter filter) {
        printSequent(seq, filter, true);
    }

    /**
     * Pretty-print a sequent.
     * The sequent arrow is rendered as <code>=&gt;</code>.  If the
     * sequent doesn't fit in one line, a line break is inserted after each
     * formula, the sequent arrow is on a line of its own, and formulae
     * are indented w.r.t. the arrow.
     * A line-break is printed after the Sequent.
     * No filtering is done.
     * @param seq The Sequent to be pretty-printed
     */
    public void printSequent(Sequent seq) {
        printSequent(seq, true);
    }


    /**
     * Pretty-prints a Semisequent.  Formulae are separated by commas.
     *
     * @param semiseq the semisequent to be printed
     */
    public void printSemisequent(Semisequent semiseq)
        throws IOException
    {
        for (int i=0;i<semiseq.size();i++) {
            markStartSub();
            printConstrainedFormula(semiseq.get(i));
            markEndSub();
            if (i!=semiseq.size()-1) {
                layouter.print(",").brk(1);
            }
        }
    }

    public void printSemisequent (ListOfSequentPrintFilterEntry p_formulas )
        throws IOException {
        IteratorOfSequentPrintFilterEntry it   = p_formulas.iterator ();
        SequentPrintFilterEntry           entry;
        int                               size = p_formulas.size     ();
        while ( size-- != 0 ) {
            entry = it.next ();
            markStartSub();
            formulaConstraint = entry.getDisplayConstraint ();
            printConstrainedFormula( entry.getFilteredFormula () );
            markEndSub();
            if ( size != 0 ) {
                layouter.print(",").brk(1);
            }
        }
        formulaConstraint = null;
    }

    /**
     * Pretty-prints a constrained formula. The constraint
     * "Constraint.BOTTOM" is suppressed
     *
     * @param cfma the constrained formula to be printed
     */
    public void printConstrainedFormula(ConstrainedFormula cfma)
        throws IOException {
                if ( cfma.constraint().isBottom() ) {
                    printTerm(cfma.formula());
                } else {
                    layouter.beginC(0);
                    layouter.ind();
                    printTerm(cfma.formula());
                    layouter.brk(1,3).print("<<").ind(1,6);
                    printConstraint(cfma.constraint());
                    layouter.end();
                }
    }

    /**
     * Pretty-prints a (shadowed) array expression
     *
     * @param arraySep usually a <code>[ </code> and a <code>] </code>
     * @param t the array expression as a whole
     * @param ass the associatives for the subterms
     */
    public void printArray(String[] arraySep, Term t, int[] ass)
        throws java.io.IOException {
        startTerm(t.arity());
        for (int i = 0;  i<2; i++) {
            maybeParens(t.sub(i), ass[i]);
            layouter.print(arraySep[i]);
            final Sort arraySortOfOperator = ((ArrayOp)t.op()).arraySort();
            if (i==1 && t.sub(0).sort() != arraySortOfOperator) {
                layouter.print("@(");
                layouter.print(arraySortOfOperator.name().toString());
                layouter.print(")");
            }
        }
        if (t.op() instanceof ShadowedOperator) {
            printTransactionNumber(t.sub(2));
        }
    }


    /**
     * Pretty-prints a location descriptor.
     */
    public void printLocationDescriptor(LocationDescriptor loc)
        throws java.io.IOException {
        
        if(loc instanceof BasicLocationDescriptor) {
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
            SetOfQuantifiableVariable boundVars = bloc.getLocTerm().freeVars();

            if(boundVars.size() > 0) {
                layouter.print("\\for ").beginC();
                printVariables(new ArrayOfQuantifiableVariable(boundVars.toArray()));
                layouter.end();
            }

            if(bloc.getFormula().op() != Op.TRUE) {
                layouter.print("\\if (").beginC();
                printTerm(bloc.getFormula());
                layouter.print(") ").end();
            }
            
            printTerm(bloc.getLocTerm());

        } else {
            Debug.assertTrue(loc instanceof EverythingLocationDescriptor);
            layouter.print("*");
        }
    }
    
    
    /**
     * Pretty-prints a set of location descriptors.
     */
    public void printLocationDescriptors(SetOfLocationDescriptor locations)
        throws java.io.IOException {
        layouter.print("{").beginC();
        IteratorOfLocationDescriptor it = locations.iterator();
        while(it.hasNext()) {
            printLocationDescriptor(it.next());
            if(it.hasNext()) {
                layouter.print(", ").brk();
            }
        }
        layouter.print("}").end();
    }


    /**
     * Pretty-print a constraint
     *
     * This does currently only work well for "EqualityConstraint"s,
     * which are printed as a list of unifications. The bottom
     * constraint doesn't get special handling in here, i.e. this
     * method should not be called for p == Constraint.BOTTOM
     */
    public void printConstraint(Constraint p)
        throws IOException
    {
        createPositionTable = false;
        if ( p instanceof EqualityConstraint ) {

            // Within the constraint metavariables should not be
            // instantiated
            Constraint frmC   = formulaConstraint;
            formulaConstraint = null;

            EqualityConstraint eqc = (EqualityConstraint)p;
            List vars = new ArrayList ();
            {
                IteratorOfMetavariable it =
                    eqc.restrictedMetavariables ();

                while ( it.hasNext () )
                    vars.add ( it.next () );
            }

            startTerm ( vars.size () );
            layouter.print("[ ").beginI(0);

            ListIterator it = vars.listIterator ();
            Metavariable mv;
            Term         inst;
            while ( it.hasNext () ) {
                mv   = (Metavariable)it.next ();
                inst = eqc.getDirectInstantiation ( mv );
                if ( inst == null )
                    inst = TermFactory.DEFAULT.createFunctionTerm ( mv );

                markStartSub();
                printInfixTerm ( TermFactory.DEFAULT.createFunctionTerm ( mv ), 15,
                                 "=",
                                 inst, 10);
                markEndSub();

                if ( it.hasNext () ) {
                    layouter.print(",").brk(1,0);
                }
            }
            layouter.print(" ]").end();

            formulaConstraint = frmC;

        } else {
            // Don't know how to pretty-print this constraint class
            layouter.print ( p.toString () );
        }
        createPositionTable = true;
    }


    /**
     * Pretty-prints a term or formula.  How it is rendered depends on
     * the NotationInfo given to the constructor.
     *
     * @param t the Term to be printed
     */
    public void printTerm(Term t)
        throws IOException {
        if(notationInfo.getAbbrevMap().isEnabled(t)){
            startTerm(0);
            layouter.print(notationInfo.getAbbrevMap().getAbbrev(t));
        } else {
            notationInfo.getNotation(t.op(), services).print(t,this);
        }
    }

    /**
     * Pretty-prints a set of terms.
     * @param terms the terms to be printed
     */
    public void printTerm(SetOfTerm terms)
        throws IOException {
        getLayouter().print("{");
        IteratorOfTerm it = terms.iterator();
        while (it.hasNext()) {
            printTerm(it.next());
            if (it.hasNext())
                getLayouter().print(", ");
        }
        getLayouter().print("}");
    }


    /**
     * Pretty-prints a term or formula in the same block.  How it is
     * rendered depends on the NotationInfo given to the constructor.
     * `In the same block' means that no extra indentation will be
     * added if line breaks are necessary.  A formula <code>a &amp; (b
     * &amp; c)</code> would print <code>a &amp; b &amp; c</code>, omitting
     * the redundant parentheses.  The subformula <code>b &amp; c</code>
     * is printed using this method to get a layout of
     *
     * <pre>
     *   a
     * &amp; b
     * &amp; c
     * </pre>
     * instead of
     * <pre>
     *   a
     * &amp;   b
     *   &amp; c
     * </pre>
     *
     *
     * @param t the Term to be printed */
    public void printTermContinuingBlock(Term t)
        throws IOException
    {
        notationInfo.getNotation(t.op(), services).printContinuingBlock(t,this);
    }


    /** Print a term in <code>f(t1,...tn)</code> style.  If the
     * operator has arity 0, no parentheses are printed, i.e.
     * <code>f</code> instead of <code>f()</code>.  If the term
     * doesn't fit on one line, <code>t2...tn</code> are aligned below
     * <code>t1</code>.
     *
     * @param name the name to be printed before the parentheses.
     * @param t the term to be printed.  */
    public void printFunctionTerm(String name,
                                  Term t)
        throws IOException
    {
        //For OCL simplification
        if (oclPrettyPrinting && PresentationFeatures.ENABLED && t.arity()>0) {
            printOCLUMLPropertyTerm(name, t);
        }
        //
        else {
            startTerm(t.arity());
            layouter.print(name);
            if(t.arity()>0 || t.op() instanceof ProgramMethod) {
                layouter.print("(").beginC(0);
                for (int i=0;i<t.arity();i++) {
                    markStartSub();
                    printTerm(t.sub(i));
                    markEndSub();

                    if (i<t.arity()-1) {
                        layouter.print(",").brk(1,0);
                    }
                }
                layouter.print(")").end();
            }
        }
    }

    public void printCast(String pre, String post,
            Term t, int ass) throws IOException {
        final CastFunctionSymbol cast = (CastFunctionSymbol)t.op();
        startTerm(t.arity());
        layouter.print(pre);
        layouter.print(cast.getSortDependingOn().toString());
        layouter.print(post);
        maybeParens(t.sub(0), ass);
    }


    /** Print a term in <code>f(t1,...tn)</code> style.  If it doesn't
     * fit on one line, <code>t2...tn</code> are aligned below t1.
     * Print a term in <code>o.q(t1,...tn)</code> style.
     *
     * @param name the name of the query
     * @param t the Term to be printed
     * @param ass the int defining the associativity of 
     * the term
     */
    public void printQueryTerm(String name,
			       Term t, 
			       int ass) 
	throws IOException
    {
	int start = 0;
	if((t.op() instanceof ProgramMethod) && (
	       ((ProgramMethod) t.op()).isStatic() || 
	       ((ProgramMethod) t.op()).isConstructor())){
	    startTerm(t.arity());
	    layouter.print(((ProgramMethod) t.op()).
			   getContainerType().getName());
	}else{
	    start = 1;
	    startTerm(t.arity());
	    maybeParens(t.sub(0), ass);
	}
	layouter.print(".").print(name).print("(").beginC(0);
	for (int i=start;i<t.arity();i++) {
	    markStartSub();
	    printTerm(t.sub(i));
	    markEndSub();
	    if (i<t.arity()-1) {
		layouter.print(",").brk(1,0);
	    }
	}
	layouter.print(")").end();
    }



    /** Print a unary term in prefix style.  For instance
     * <code>!a</code>.  No line breaks are possible.
     *
     * @param name the prefix operator
     * @param t    the subterm to be printed
     * @param ass  the associativity for the subterm
     */
    public void printPrefixTerm(String name,
                                Term t,int ass)
        throws IOException
    {
        startTerm(1);
        layouter.print(name);
        maybeParens(t, ass);
    }


    /** Print a unary term in postfix style.  For instance
     * <code>t.a</code>, where <code>.a</code> is the postfix operator.
     * No line breaks are possible.
     *
     * @param name the postfix operator
     * @param t    the subterm to be printed
     * @param ass  the associativity for the subterm
     */
     public void printPostfixTerm(Term t,int ass,String name)
        throws IOException
    {
        startTerm(1);
        maybeParens(t, ass);
        layouter.print(name);
    }

    /**
     * Pretty-prints a shadowed attribute
     * @param t1 the attribute prefix
     * @param ass1  the associativity for the reference prefix
     * @param name the attribute name
     * @param t2 the shadow number term
     */
    public void printShadowedAttribute(Term t1, int ass1, String name,
                                       Term t2)
        throws java.io.IOException {
        startTerm(2);
        maybeParens(t1, ass1);
        layouter.print(name);
        printTransactionNumber(t2);
    }



    /** Print a binary term in infix style.  For instance <code>p
     * &amp; q</code>, where <code>&amp;</code> is the infix
     * operator.  If line breaks are necessary, the format is like
     *
     * <pre>
     *   p
     * & q
     * </pre>
     *
     * The subterms are printed using
     * {@link #printTermContinuingBlock(Term)}.
     *
     * @param l    the left subterm
     * @param assLeft associativity for left subterm
     * @param name the infix operator
     * @param r    the right subterm
     * @param assRight associativity for right subterm
     */
    public void printInfixTerm(Term l,int assLeft,
                               String name,
                               Term r,int assRight)
        throws IOException
    {
        int indent = name.length()+1;
        layouter.beginC(indent);
        printInfixTermContinuingBlock(l,assLeft,
                                      name,
                                      r,assRight);
        layouter.end();
    }

    /** Print a binary term in infix style, continuing a containing
     * block.  See {@link #printTermContinuingBlock(Term)} for the
     * idea.  Otherwise like
     * {@link #printInfixTerm(Term,int,String,Term,int)}.
     *
     * @param l    the left subterm
     * @param assLeft associativity for left subterm
     * @param name the infix operator
     * @param r    the right subterm
     * @param assRight associativity for right subterm
     * */
    public void printInfixTermContinuingBlock(Term l,int assLeft,
                                              String name,
                                              Term r,int assRight)
        throws IOException
    {
        int indent = name.length()+1;
        startTerm(2);
        layouter.ind();
        maybeParens(l, assLeft);
        layouter.brk(1,-indent).print(name).ind(1,0);
        maybeParens(r, assRight);
    }

    /**
     * prints an anonymous update
     */
    public void printAnonymousUpdate(Term t, int ass)
    throws IOException {
        mark(MARK_START_UPDATE);
        layouter.beginC(2).print("{");
        startTerm(1);
        layouter.print(t.op().name().toString());
        layouter.print("}");
        mark(MARK_END_UPDATE);
        layouter.brk(1);
        maybeParens(t.sub(t.arity()-1), ass);
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

    public void printQuanUpdateTerm (String l,
                                     String asgn,
                                     String r,
                                     Term t,
                                     int ass1,
                                     int ass2,
                                     int ass3) throws IOException {
        final QuanUpdateOperator op = (QuanUpdateOperator)t.op ();
        mark(MARK_START_UPDATE);
        layouter.beginC ( 2 ).print ( l );
        startTerm ( t.arity () );
        for ( int i = 0; i < op.locationCount (); i++ ) {
            final Operator loc = op.location ( i );

            layouter.beginC(0);
            printUpdateQuantification ( t, op, i );

            final String[] separator = setupUpdateSeparators ( loc,
                                                               op.location(t, i));
            for ( int j = loc.arity (); j >= 1; j-- ) {
                final Term sub = t.sub ( op.valuePos ( i ) - j );

                if (loc instanceof ShadowedOperator && j == 1) {
                    printTransactionNumber(sub);
                } else {
                    markStartSub ();
                    printTerm ( sub );
                    markEndSub ();
                    layouter.print ( separator[loc.arity () - j] );
                }
            }
            layouter.print ( asgn ).brk(0,0);
            layouter.end();
            maybeParens ( op.value ( t, i ), ass2 );
            if ( i < op.locationCount () - 1 ) {
                layouter.print ( " ||" ).brk ( 1, 0 );
            }
        }

        layouter.print ( r );
        mark(MARK_END_UPDATE);
        layouter.brk ( 0 );
        maybeParens ( t.sub ( t.arity () - 1 ), ass3 );
        layouter.end ();
    }

    /**
     * @param sub
     * @throws IOException
     */
    private void printTransactionNumber(final Term sub) throws IOException {
        final int primes =  asPrimes ( sub );
        if ( primes == -1 ) {
            layouter.print ( "^(" );
            markStartSub ();
            printTerm ( sub );
            markEndSub ();
            layouter.print ( ")" );
        } else {
            final StringBuffer s_primes = new StringBuffer();
            for (int p = 0; p<primes; p++) {
                s_primes.append("\'");
            }
            markStartSub ();
            markEndSub ();
            layouter.print(s_primes.toString());

        }
    }


    private void printUpdateQuantification (Term t,
                                            QuanUpdateOperator op,
                                            int locationNum) throws IOException {
        final ArrayOfQuantifiableVariable boundVars =
            t.varsBoundHere ( op.valuePos ( locationNum ) );
        if ( boundVars.size () > 0 ) {
            layouter.print ( "\\for " );
            printVariables ( boundVars );
        }

        if ( op.guardExists ( locationNum ) ) {
            layouter.print ( "\\if (" ).beginC ( 0 );
            markStartSub ();
            printTerm ( t.sub ( op.guardPos ( locationNum ) ) );
            markEndSub ();
            layouter.print ( ") " ).end ();
        }
    }

    protected void printVariables (ArrayOfQuantifiableVariable vars)
                                            throws IOException {
        int size = vars.size ();
        if(size != 1)
          layouter.print ( "(" );
        for ( int j = 0; j != vars.size (); ) {
            final QuantifiableVariable v = vars.getQuantifiableVariable ( j );
            if(v instanceof LogicVariable){
                Term t =
                    TermFactory.DEFAULT.createVariableTerm((LogicVariable) v);
                if(notationInfo.getAbbrevMap().containsTerm(t)){
                    layouter.print (v.sort().name().toString() + " " +
                                    notationInfo.getAbbrevMap().getAbbrev(t));
                }else{
                    layouter.print ( v.sort().name() + " " + v.name ());
                }
            }else{
                layouter.print ( v.name ().toString());
            }
            ++j;
            if ( j != vars.size () ) layouter.print ( "; " );
        }
        if(size != 1)
          layouter.print ( ") " );
        else
          layouter.print ( "; " );
    }


    private int asPrimes(Term shadowNum) {
        int result = 0;
        Term t = shadowNum;        
        if (services == null || t.op() != services.getTypeConverter()
        					  .getIntegerLDT()
        					  .getNumberSymbol()) {
            return -1;
        }


        final String numberString =
            Notation.NumLiteral.printNumberTerm(t);
        if (numberString == null) {
            result = -1;
        } else {
            try {
                result = Integer.parseInt(numberString);
            } catch (NumberFormatException nfe) {
                result = -1;
            }
        }
        return result>0 ? result : -1;

    }

    String[] setupUpdateSeparators (final Operator loc, final Term t)
                                                throws IOException {
        String[] separator = new String [loc.arity ()];
        if ( loc instanceof AttributeOp ) {
            separator[0] = Notation.
               Attribute.printName(((AttributeOp)loc), t.sub(0), this);
        } else if ( loc instanceof ArrayOp ) {
            separator[0] = "[";
            separator[1] = "]";
        } else if ( loc.arity () == 0 ) {
            layouter.print( loc.name ().toString ().replaceAll ( "::", "." ) );
        } else {
            layouter.print ( loc.name().toString() + "(" );
            for ( int m = 0; m < loc.arity () - 1; m++ ) {
                separator[m] = ",";
            }
            separator[loc.arity () - 1] = ")";
        }
        return separator;
    }

  
    public void printIfThenElseTerm(Term t, String keyword) throws IOException {
        startTerm(t.arity());

        layouter.beginC ( 0 );

        layouter.print ( keyword );

        if ( t.varsBoundHere ( 0 ).size () > 0 ) {
            layouter.print ( " " );
            printVariables ( t.varsBoundHere ( 0 ) );
        }
        layouter.print( " (" );
        markStartSub ();
        printTerm ( t.sub ( 0 ) );
        markEndSub ();
        layouter.print ( ")" );

        for (int i = 1; i < t.arity(); ++i) {
            layouter.brk(1, 3);
            if (i == 1) {
                layouter.print ( " \\then (" );
            } else {
                layouter.print ( " \\else (" );
            }
            markStartSub ();
            printTerm ( t.sub ( i ) );
            markEndSub ();
            layouter.print ( ")" );
        }

        layouter.end();
    }


    /** Print a substitution term.  This looks like
     * <code>{var/t}s</code>.  If line breaks are necessary, the
     * format is
     *
     * <pre>
     * {var/t}
     *   s
     * </pre>
     *
     * @param l       the String used as left brace symbol
     * @param v       the {@link QuantifiableVariable} to be substituted
     * @param t       the Term to be used as new value 
     * @param ass2    the int defining the associativity for the new value
     * @param r       the String used as right brace symbol
     * @param phi     the substituted term/formula
     * @param ass3    the int defining the associativity for phi
     */
    public void printSubstTerm(String l,
                               QuantifiableVariable v,
                               Term t,int ass2,
                               String r,
                               Term phi,int ass3)
        throws IOException
    {
        layouter.beginC(2).print(l);
        printVariables(new ArrayOfQuantifiableVariable(v));
        startTerm(2);
        maybeParens(t, ass2);
        layouter.print(r).brk(0);
        maybeParens(phi, ass3);
        layouter.end();
    }


    /** Print a quantified term.  Normally, this looks like
     * <code>all x:s.phi</code>.  If line breaks are necessary,
     * the format is
     *
     * <pre>
     * all x:s.
     *   phi
     * </pre>
     *
     * Note that the parameter <code>var</code> has to contain the
     * variable name with colon and sort.
     *
     * @param name the name of the quantifier
     * @param var  the quantified variable (+colon and sort)
     * @param sep  the separator (usually a dot)
     * @param phi  the quantified formula
     * @param ass  associativity for phi
     */
    public void printQuantifierTerm(String name,
                                    ArrayOfQuantifiableVariable vars,
                                    Term phi, int ass)
        throws IOException
    {
        layouter.beginC(2);
        layouter.print(name).print(" ");
        printVariables(vars);
        layouter.brk();
        startTerm(1);
        maybeParens(phi,ass);
        layouter.end();
    }



    /** Print a constant.  This just prints the string <code>s</code> and
     * marks it as a nullary term.
     *
     * @param s the constant
     */
    public void printConstant(String s)
        throws IOException {

        startTerm(0);
        layouter.print(s);
    }


    /** 
     * Prints a metavariable. If the  {@link #formulaConstraint} 
     * contains an instantiation for the metavariable the instantiation
     * is printed rather than the metavariable itself.
     * 
     * @param p_mv the Metavariable to be printed
     *  
     */
    public void printMetavariable ( Metavariable p_mv )
    throws IOException
        {
        if ( formulaConstraint != null ) {
                Term t = formulaConstraint.getInstantiation ( p_mv );
                if ( t.op () != p_mv ) {
                        printTerm ( t );
                        return;
                }
        }

        printConstant ( p_mv.name().toString() );
    }


    /**
     * Print a Java block.  This is formatted using the ProgramPrinter
     * given to the constructor.  The result is indented according to
     * the surrounding material.  The first `executable' statement is
     * marked for highlighting.
     *
     * @param j the Java block to be printed
     */
    public void printJavaBlock(JavaBlock j)
        throws IOException
    {
        java.io.StringWriter sw = new java.io.StringWriter();
        prgPrinter.reset();
        prgPrinter.setWriter(sw);
        Range r=null;
        try {
            j.program().prettyPrint(prgPrinter);
            r = prgPrinter.getRangeOfFirstExecutableStatement();
        } catch (java.io.IOException e) {
            layouter.print("ERROR");
            System.err.println("Error while printing Java program \n"+e);
            throw new RuntimeException(
                               "Error while printing Java program \n"+e);
        }
        // send first executable statement range
        printMarkingFirstStatement(sw.toString(),r);

    }

    /** Print a string marking a range as first statement.  The range
     * <code>r</code> indicates the `first statement' character range in
     * string <code>s</code>.  This is sent to the layouter by decomposing
     * <code>s</code> into parts and using the appropriate
     * {@link de.uka.ilkd.key.util.pp.Layouter#mark(Object)} calls.
     * This solves the problem that the material in <code>s</code> might
     * be further indented.
     *
     * @param s   the string containing a program
     * @param r   the range of the first statement
     */
    private void printMarkingFirstStatement(String s,Range r)
        throws IOException    {

        int iEnd   = r.end()<=s.length()?r.end():s.length();
        int iStart = r.start()<=iEnd?r.start():iEnd;
        String start = s.substring(0, iStart);
        String firstStmt = s.substring(iStart, iEnd);
        String end = s.substring(iEnd);
        layouter.beginC(0);
        printVerbatim(start);
        mark(MARK_START_FIRST_STMT);
        printVerbatim(firstStmt);
        mark(MARK_END_FIRST_STMT);
        printVerbatim(end);
        layouter.end();
    }

    /** Print a string containing newlines to the layouter.  This is like
     * {@link de.uka.ilkd.key.util.pp.Layouter#pre(String)}, but
     * no block is opened.
     */
    private void printVerbatim(String s)
        throws IOException
    {
        StringTokenizer st = new StringTokenizer(s,"\n",true);
        while(st.hasMoreTokens()) {
            String line = st.nextToken();
            if ("\n".equals(line)) {
                layouter.nl();
            } else {
                layouter.print(line);
            }
        }
    }


    /** Print a DL modality formula.  <code>phi</code> is the whole
     * modality formula, not just the subformula inside the modality.
     * Normally, this looks like
     * <code>&lt;Program&gt;psi</code>, where <code>psi = phi.sub(0)</code>.
     * No line breaks are inserted, as the program itself is always broken.
     * In case of a program modality with arity greater than 1,
     * the subformulae are listed between parens, like
     * <code>&lt;Program&gt;(psi1,psi2)</code>
     */

    public void printModalityTerm(String left,
                                  JavaBlock jb,
                                  String right,
                                  Term phi,
                                  int ass)
        throws IOException {
        if (phi.op() instanceof ModalOperatorSV) {
            Object o = getInstantiations().getInstantiation((ModalOperatorSV) phi.op());
            if (o == null) {
                logger.debug("PMT  NO  " + phi + " @[ " + phi.op() + " ]@ " + " is : " +
                             phi.getClass().getName() + " @[" + phi.op().getClass().getName() + "]@ known");
            } else {
                //logger.debug("Instantiation of " + phi + " @[" + phi.op() + "]@" + " is : " + o + o.getClass().getName());
                //logger.debug(getInstantiations());
                logger.debug("PMT YES " + phi.op() + " -> " + o
                             + " @[" + o.getClass().getName() + "]@");

                if(notationInfo.getAbbrevMap().isEnabled(phi)){
                    startTerm(0);
                    layouter.print(notationInfo.getAbbrevMap().getAbbrev(phi));
                } else {
                    Term[] ta = new Term[phi.arity()];
                    for (int i = 0; i < phi.arity(); i++) {
                        ta[i] = phi.sub(i);
                    }
                    ArrayOfQuantifiableVariable[] aa = new ArrayOfQuantifiableVariable[phi.arity()];
                    for (int i = 0; i < phi.arity(); i++) {
                        aa[i] = phi.varsBoundHere(i);
                    }
                    Term term = TermFactory.DEFAULT.
			createTerm((Modality)o, ta, aa, phi.javaBlock());
                    notationInfo.getNotation((Modality)o, services).print(term, this);
                    return;
                }

            }
        }

        mark(MARK_MODPOSTBL);
        startTerm(phi.arity());
        layouter.print(left);
        printJavaBlock(jb);

        layouter.print(right+" ");
        if(phi.arity() == 1) {
            maybeParens(phi.sub(0),ass);
        } else if(phi.arity()>1) {
            layouter.print("(");
            for (int i=0;i<phi.arity();i++) {
                markStartSub();
                printTerm(phi.sub(i));
                markEndSub();
                if (i<phi.arity()-1) {
                    layouter.print(",").brk(1,0);
                }
            }
            layouter.print(")");
        }
    }

    /**
     * Used for OCL Simplification.
     */
    public void printOCLWrapperTerm(Term t) throws IOException {
        oclPrettyPrinting = true;
        startTerm(1);
        markStartSub();
        printTerm(t.sub(0));
        markEndSub();
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints iterate expressions.
     * "collection->iterate(elem:T1 ; acc:T2=init | expr(elem, acc))"
     */
    public void printOCLIterateTerm(Term collection,
                                    String arrow,
                                    String name,
                                    String leftParens,
                                    String iterVarDecl,
                                    String sep1,
                                    String accVarDecl,
                                    String equals,
                                    Term accVarInit,
                                    String sep2,
                                    Term expr,
                                    String rightParens) throws IOException {
        startTerm(3);
        layouter.beginC(0);
        layouter.beginI(0);
        markStartSub();
        printTerm(collection);
        markEndSub();
        layouter.print(arrow).brk(0,2).print(name).end();
        layouter.print(leftParens);
        layouter.print(iterVarDecl).print(sep1);
        layouter.brk(1,5);
        layouter.print(accVarDecl).print(equals);
        markStartSub();
        printTerm(accVarInit);
        markEndSub();
        layouter.print(sep2);
        layouter.brk(1,5);
        markStartSub();
        printTerm(expr);
        markEndSub();
        layouter.print(rightParens).end();
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints Collection operation expressions with one iteration variable.
     * "collection->forAll(elem:T | expr(elem))"
     */
    public void printOCLCollOpBoundVarTerm(Term collection,
                                           String arrow,
                                           String name,
                                           String leftParens,
                                           String iterVarDecl,
                                           String sep,
                                           Term expr,
                                           String rightParens) throws IOException {
        startTerm(2);
        layouter.beginC(0);
        layouter.beginI(0);
        markStartSub();
        printTerm(collection);
        markEndSub();
        layouter.print(arrow).brk(0,2).print(name).end();
        layouter.print(leftParens);
        layouter.print(iterVarDecl).print(sep);
        layouter.brk(1,5);
        markStartSub();
        printTerm(expr);
        markEndSub();
        layouter.print(rightParens).end();
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints Collection operation expressions without iteration variable.
     * "collection->includes(object)"
     */
    public void printOCLCollOpTerm(String name, Term t) throws IOException {
        startTerm(t.arity());
        markStartSub();
        printTerm(t.sub(0));
        markEndSub();
        layouter.print("->").print(name).print("(").beginC(0);
        for (int i=1;i<t.arity();i++) {
            markStartSub();
            printTerm(t.sub(i));
            markEndSub();
            if (i<t.arity()-1) {
                layouter.print(",").brk(1,0);
            }
        }
        layouter.print(")").end();
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints if-then-else-endif expressions.
     */
    public void printOCLIfTerm(String ifS,
                               Term ifT,
                               String thenS,
                               Term thenT,
                               String elseS,
                               Term elseT,
                               String endif) throws IOException {
        startTerm(3);
        layouter.beginC(0);
        layouter.print(ifS);
        markStartSub();
        printTerm(ifT);
        markEndSub();
        layouter.brk(1,1).print(thenS);
        markStartSub();
        printTerm(thenT);
        markEndSub();
        layouter.brk(1,1).print(elseS);
        markStartSub();
        printTerm(elseT);
        markEndSub();
        layouter.brk(1,0).print(endif).end();
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints Collection expressions.
     * "Set{Alpha, Beta, Gamma}"
     */
    public void printOCLCollectionTerm(Term t) throws IOException {
        startTerm(2);
        markStartSub();
        printTerm(t.sub(0));
        markEndSub();
        if (t.sub(1).op() == OclOp.EMPTY_SET
            || t.sub(1).op() == OclOp.EMPTY_BAG
            || t.sub(1).op() == OclOp.EMPTY_SEQUENCE) {
            markStartSub();
            layouter.print("");
            markEndSub();
        } else if (t.sub(1).op() == OclOp.INSERT_SET
                 || t.sub(1).op() == OclOp.INSERT_BAG
                 || t.sub(1).op() == OclOp.INSERT_SEQUENCE) {
            layouter.print(",").brk(1,2);
            markStartSub();
            printOCLCollectionTerm(t.sub(1));
            markEndSub();
        } else {
            layouter.print(",").brk(1,2);
            markStartSub();
            printTerm(t.sub(1));
            markEndSub();
        }
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints references to UML properties.
     * "self.queryMethod()"
     */
    public void printOCLUMLPropertyTerm(String name, 
                                        Term t) throws IOException {
	int index = name.indexOf("+~");
	if (index == -1) {
	    String attribute = "." + name.substring(name.lastIndexOf("~")+1);
	    printPostfixTerm(t.sub(0), 80, attribute);
	} else {
	    String temp = name.substring(0, index);
	    String method = temp.substring(temp.lastIndexOf("~")+1);
	    printQueryTerm(method, t, 121);
	}
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints list of OCL constraints.
     * "context <Context> inv:
     *    <the invariant>"
     */
    public void printOCLInvariantTerm(Term context,
                                      Term invariant) throws IOException {
        startTerm(2);
        layouter.beginC(0);
        layouter.print("context ");
        markStartSub();
        printTerm(context);
        markEndSub();
        layouter.print(" inv:").brk(1,3);
        markStartSub();
        printTerm(invariant);
        markEndSub();
        layouter.end();
    }

    /**
     * Used for OCL Simplification.
     * Pretty-prints OCL constraints.
     * "context <Context1> inv:
     *    <invariant1>
     *
     *  context <Context2> inv:
     *    <invariant2>"
     */
    public void printOCLListOfInvariantsTerm(Term t) throws IOException {
        if (t.arity() > 0) {
            startTerm(2);
            markStartSub();
            printTerm(t.sub(0));
            markEndSub();
            if (t.sub(1).op() == OclOp.NIL_INV) {
                markStartSub();
                layouter.print("");
                markEndSub();
            } else {
                layouter.print("\n\n").brk(0,0);
                markStartSub();
                printOCLListOfInvariantsTerm(t.sub(1));
                markEndSub();
            }
        }
    }

    /**
     * Returns the pretty-printed sequent.  This should only be called
     * after a <tt>printSequent</tt> invocation returns.
     *
     * @return the pretty-printed sequent.
     */
    public String toString() {
        try {
            layouter.flush();
        } catch (IOException e) {
            throw new RuntimeException (
              "IO Exception in pretty printer:\n"+e);
        }
        return ((PosTableStringBackend)backend).getString()+"\n";
    }

    /**
     * Returns the pretty-printed sequent in a StringBuffer.  This
     * should only be called after a <tt>printSequent</tt> invocation
     * returns.
     *
     * @return the pretty-printed sequent.  
     */
    public StringBuffer result() {
        try {
            layouter.flush();
        } catch (IOException e) {
            throw new RuntimeException (
              "IO Exception in pretty printer:\n"+e);
        }
        return new StringBuffer(((PosTableStringBackend)backend).getString()).append("\n");
    }

    protected Layouter mark(Object o) {
        if (pure) {
                return null;
        } else {
                return layouter.mark(o);
        }
    }

    /**
     * returns the PositionTable representing position information on
     * the sequent of this LogicPrinter. Subclasses may overwrite
     * this method with a null returning body if position information
     * is not computed there.
     */
    public InitialPositionTable getPositionTable() {
        if (pure) {
            return null;
        }
        return ((PosTableStringBackend)backend).getPositionTable();
    }

    /** Returns the ProgramPrinter
     * @return the ProgramPrinter
     */
    public ProgramPrinter programPrinter() {
        return prgPrinter;
    }

    /** Returns the Layouter
     * @return the Layouter
     */
    protected Layouter getLayouter() {
        return layouter;
    }


    /**
     * Prints a subterm, if needed with parentheses.  Each subterm has
     * a Priority. If the priority is less than the associativity for
     * that subterm fixed by the Notation/NotationInfo, parentheses
     * are needed.
     *
     * <p>If prio and associativity are equal, the subterm is printed
     * using {@link #printTermContinuingBlock(Term)}.  This currently
     * only makes a difference for infix operators.
     *
     * @param t   the the subterm to print
     * @param ass the associativity for this subterm */
    protected void maybeParens(Term t, int ass)
        throws IOException
    {
        if (t.op() instanceof SchemaVariable && instantiations != null &&
	    instantiations.getInstantiation((SchemaVariable)t.op()) 
	    instanceof Term) {
	    t = (Term) instantiations.getInstantiation((SchemaVariable)t.op());
	}
	    
	if (notationInfo.getNotation(t.op(), services).getPriority() < ass){	    
	    markStartSub();
	    layouter.print("(");   
	    printTerm(t);	   
	    layouter.print(")");
	    markEndSub();
	} else {
	    markStartSub();
	    if (notationInfo.getNotation(t.op(), services).getPriority() == ass) {
		printTermContinuingBlock(t);
	    } else {
		printTerm(t);
	    }
	    markEndSub();
	}
    }

    /**
     * @return The SVInstantiations given with the last printTaclet call.
     */
    public SVInstantiations getInstantiations() {
        return instantiations;
    }

    /** Mark the start of a subterm.  Needed for PositionTable construction.*/
    private static final Object MARK_START_SUB = new Object();
    /** Mark the end of a subterm.  Needed for PositionTable construction.*/
    private static final Object MARK_END_SUB = new Object();
    /** Mark the start of a term with a number of subterms.
     * Needed for PositionTable construction.*/
    private static final Object MARK_START_TERM = new Object();
    /** Mark the start of the first executable statement.
     * Needed for PositionTable construction.*/
    private static final Object MARK_START_FIRST_STMT = new Object();
    /** Mark the end of the first executable statement.
     * Needed for PositionTable construction.*/
    private static final Object MARK_END_FIRST_STMT = new Object();
    /** Mark the need for a ModalityPositionTable.  The next
     * startTerm mark will construct a ModalityPositionTable
     * instead of the usual PositionTable.
     * Needed for PositionTable construction.*/
    private static final Object MARK_MODPOSTBL = new Object();
    /** Mark the start of an update.*/
    private static final Object MARK_START_UPDATE = new Object();
    /** Mark the end of an update.*/
    private static final Object MARK_END_UPDATE = new Object();

    private boolean createPositionTable = true;

    /**
     * Called before a substring is printed that has its own entry in
     * a position table.  The method sends a mark to the layouter,
     * which will make the backend set a start entry in posTbl, push a
     * new StackEntry with the current posTbl and current pos on the
     * stack and set the current pos to the length of the current
     * string result. Subclasses may overwrite this method with an
     * empty body if position information is not needed there.
     */
    protected void markStartSub() {
        if (createPositionTable) {
            mark(MARK_START_SUB);
        }
    }

    /**
     * Called after a substring is printed that has its own entry in a
     * position table.  The backend will finishes the position table
     * on the top of the stack and set the entry on the top of the
     * stack to be the current position/position table. Subclasses may
     * overwrite this method with an empty body if position
     * information is not needed there.
     */
    protected void markEndSub() {
        if (createPositionTable) {
            mark(MARK_END_SUB);
        }
    }

    /**
     * Start a term with subterms.  The backend will set the current
     * posTbl to a newly created position table with the given number
     * of rows. Subclasses may overwrite this method with an empty
     * body if position information is not needed there.
     *
     * @param size the number of rows of the new position table
     */
    protected void startTerm(int size) {
        if (createPositionTable) {
            mark(new Integer(size));
        }
    }


    /**
     * returns true if an attribute term shall be printed in short form.
     * In opposite to the other <tt>printInShortForm</tt> methods
     * it takes care of meta variable instantiations
     * @param attributeProgramName the String of the attribute's program
     * name
     * @param t the Term used as reference prefix
     * @return true if an attribute term shall be printed in short form.
     */
    public boolean printInShortForm(String attributeProgramName,
                                    Term t) {
        final Sort prefixSort;
        if (t.op() instanceof Metavariable) {
            Metavariable mv = (Metavariable)t.op();
            if ( formulaConstraint != null ) {
                    prefixSort =
                        formulaConstraint.getInstantiation (mv).sort();
            } else {
                prefixSort = t.sort();
            }
        } else {
            prefixSort = t.sort();
        }
        return printInShortForm(attributeProgramName, prefixSort);
    }


    /**
     * tests if the program name together with the prefix sort
     * determines the attribute in a unique way
     * @param programName the String denoting the program name of
     * the attribute
     * @param sort the ObjectSort in whose reachable hierarchy
     * we test for uniqueness
     * @return true if the attribute is uniquely determined
     */
    public boolean printInShortForm(String programName, Sort sort) {
        return printInShortForm(programName, sort, services);
    }

    /**
     * escapes special characters by their HTML encoding 
     * @param text the String to be displayed as part of an HTML side
     * @return the text with special characters replaced
     */
    public static String escapeHTML(String text) {
         StringBuffer sb = new StringBuffer();
        
         for (int i = 0, sz = text.length(); i < sz; i++) {
             char c = text.charAt(i); 
             switch (c) {
             case  '<':
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
             default:
                 sb.append(c);
             }
             
         }
         return sb.toString();
    }


    /**
     * tests if the program name together with the prefix sort
     * determines the attribute in a unique way
     * @param programName the String denoting the program name of
     * the attribute
     * @param sort the ObjectSort specifying the hierarchy
     * where to test for uniqueness
     * @param services the Services class used to access the type hierarchy
     * @return true if the attribute is uniquely determined
     */
    public static boolean printInShortForm(String programName, Sort sort,
                                   Services services) {
        if ( ! ( services != null && sort != Sort.NULL && sort instanceof ObjectSort ) )
            return false;
        final KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
        assert kjt != null : "Did not find KeYJavaType for " + sort;
        return 
            services.getJavaInfo().getAllAttributes(programName, kjt).size() == 1;
    }

    /** Utility class for stack entries containing the position table
     * and the position of the start of the subterm in the result.  */
    private class StackEntry {

        PositionTable posTbl;
        int p;

        StackEntry(PositionTable posTbl, int p) {
            this.posTbl=posTbl;
            this.p=p;
        }

        PositionTable posTbl() {
            return posTbl;
        }

        int pos() {
            return p;
        }

    }

    /** A {@link de.uka.ilkd.key.util.pp.Backend} which puts its
     * result in a StringBuffer and builds a PositionTable.  Position
     * table construction is done using the {@link
     * de.uka.ilkd.key.util.pp.Layouter#mark(Object)} facility of the
     * layouter with the various static <code>MARK_</code> objects
     * declared {@link LogicPrinter}.
     */
    private class PosTableStringBackend extends StringBackend {

        /** The top PositionTable */
        private InitialPositionTable initPosTbl =
            new InitialPositionTable();

        /** The resulting position table or an intermediate result */
        private PositionTable posTbl= initPosTbl;

        /** The position in result where the current subterm starts */
        private int pos = 0;

        /** The stack of StackEntry representing the nodes above
         * the current subterm */
        private Stack stack = new Stack();

        /** If this is set, a ModalityPositionTable will
         * be built next.
         */
        private boolean need_modPosTable = false;

        /** These two remember the range corresponding to the first
         * executable statement in a JavaBlock */
        private int firstStmtStart;
        private Range firstStmtRange;

        /** Remembers the start of an update to create a range */
        private int updateStart;

        PosTableStringBackend(int lineWidth) {
            super(lineWidth);
        }

        /** Returns the constructed position table.
         *  @return the constructed position table
         */
        public InitialPositionTable getPositionTable() {
            return initPosTbl;
        }


        private void setupModalityPositionTable(StatementBlock block) {
            int count = block.getStatementCount();
            int position=0;
            for (int i=0; i<count; i++){
                posTbl.setStart(position);
                position += block.getStatementAt(i).
                    toString().length();
                posTbl.setEnd(position-1, null);
            }
        }

        /** Receive a mark and act appropriately.
         */
        public void mark(Object o) {

            // IMPLEMENTATION NOTE
            //
            // This if-cascade is really ugly.  In paricular the part
            // which says <code>instanceof Integer</code>, which stand
            // for a startTerm with given arity.
            //
            // The alternative would be to 1.: spread these
            // mini-functionalties across several inner classes in a
            // visitor-like style, effectively preventing anybody from
            // finding out what happens, and 2.: allocate separate
            // objects for each startTerm call to wrap the arity.
            //
            // I (MG) prefer it this way.
            if ( o==MARK_START_SUB ) {
                posTbl.setStart(count()-pos);
                stack.push(new StackEntry(posTbl, pos));
                pos=count();
            } else if ( o==MARK_END_SUB ) {
                StackEntry se=(StackEntry)stack.peek();
                stack.pop();
                pos=se.pos();
                se.posTbl().setEnd(count()-pos, posTbl);
                posTbl=se.posTbl();
            } else if ( o==MARK_MODPOSTBL ) {
                need_modPosTable = true;
            } else if ( o instanceof Integer ) {
                // This is sent by startTerm
                int rows = ((Integer)o).intValue();
                if (need_modPosTable) {
                    posTbl = new ModalityPositionTable(rows);
                } else {
                    posTbl = new PositionTable(rows);
                }
                need_modPosTable = false;
            } else if ( o==MARK_START_FIRST_STMT ) {
                firstStmtStart = count()-pos;
            } else if ( o==MARK_END_FIRST_STMT ) {
                firstStmtRange = new Range(firstStmtStart,
                                           count()-pos);
                ((ModalityPositionTable)posTbl)
                    .setFirstStatementRange(firstStmtRange);
            } else if ( o==MARK_START_UPDATE ) {
                updateStart = count();
            } else if ( o==MARK_END_UPDATE ) {
                initPosTbl.addUpdateRange(new Range(updateStart, count()));
            }
        }
    }
}
