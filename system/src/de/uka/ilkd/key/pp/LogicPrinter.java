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


package de.uka.ilkd.key.pp;

import java.io.IOException;
import java.io.StringWriter;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Stack;
import java.util.StringTokenizer;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.OpCollector;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.op.UpdateJunctor;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.AntecTaclet;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NewDependingOn;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.NotFreeIn;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.AntecSuccTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
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
public final class LogicPrinter {

    /**
     * The default and minimal value o fthe
     * max. number of characters to put in one line
     */
    public static final int DEFAULT_LINE_WIDTH = 55;

    /** The max. number of characters to put in one line */
    private int lineWidth = DEFAULT_LINE_WIDTH;

    /**
     * The ProgramPrinter used to pretty-print Java blocks in
     * formulae.
     */
    private ProgramPrinter prgPrinter;

    /** Contains information on the concrete syntax of operators. */
    private final NotationInfo notationInfo;

    /** the services object */
    private final Services services;

    /** This chooses the layout. */
    private Layouter layouter;

    /** The backend <code>layouter</code> will write to. */
    private Backend backend;

    /**If pure is true the PositionTable will not be calculated */
    private boolean pure = false;

    private SVInstantiations instantiations
    	= SVInstantiations.EMPTY_SVINSTANTIATIONS;
    
    
    public static String quickPrintTerm(Term t, Services services) {
        final NotationInfo ni = new NotationInfo();
        if (services != null) {
            ni.refresh(services);
        }
        LogicPrinter p = new LogicPrinter(new ProgramPrinter(), 
                                          ni, 
                                          services);
        try {
            p.printTerm(t);
        } catch (IOException ioe) {
            return t.toString();
        }
        return p.result().toString();
    }
    
    public static String quickPrintSemisequent(Semisequent s, Services services) {
        final NotationInfo ni = new NotationInfo();
        if (services != null) {
            ni.refresh(services);
        }
        LogicPrinter p = new LogicPrinter(new ProgramPrinter(), 
                                          ni, 
                                          services);

        try {
			p.printSemisequent(s);
		} catch (IOException e) {
			return s.toString();
		}
        return p.result().toString();
    }
    
    
    public static String quickPrintSequent(Sequent s, Services services) {
        final NotationInfo ni = new NotationInfo();
        if (services != null) {
            ni.refresh(services);
        }
        LogicPrinter p = new LogicPrinter(new ProgramPrinter(), 
                                          ni, 
                                          services);
        p.printSequent(s);
        return p.result().toString();
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
	this.layouter     = new Layouter(backend,2);
	this.prgPrinter   = prgPrinter;
	this.notationInfo = notationInfo;
	this.services     = services;
	this.pure         = purePrint;
	if(services != null) {
	    notationInfo.refresh(services);
	}
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
	this(prgPrinter, 
             notationInfo, 
             new PosTableStringBackend(DEFAULT_LINE_WIDTH), 
             services, 
             false);
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
	this(prgPrinter, 
	     notationInfo,
	     new PosTableStringBackend(DEFAULT_LINE_WIDTH), 
	     services,
	     purePrint);
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
    public void update(Sequent seq, 
	    	       SequentPrintFilter filter,
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
    
    
    private static void collectSchemaVarsHelper(Sequent s, OpCollector oc) {
	for(SequentFormula cf : s) {
	    cf.formula().execPostOrder(oc);
	}
    }
    
    
    private static Set<SchemaVariable> collectSchemaVars(Taclet t) {
	
	Set<SchemaVariable> result = new HashSet<SchemaVariable>();
	OpCollector oc = new OpCollector();
	
	//find, assumes
	for(SchemaVariable sv: t.getIfFindVariables()) {
	    result.add(sv);
	}
		
	//add, replacewith
	for(TacletGoalTemplate tgt : t.goalTemplates()) {
	    collectSchemaVarsHelper(tgt.sequent(), oc);
	    if(tgt instanceof AntecSuccTacletGoalTemplate) {
		collectSchemaVarsHelper(
			((AntecSuccTacletGoalTemplate)tgt).replaceWith(), oc);
	    } else if(tgt instanceof RewriteTacletGoalTemplate) {
		((RewriteTacletGoalTemplate)tgt).replaceWith()
					        .execPostOrder(oc);
	    }
	}
	
	for(Operator op : oc.ops()) {
	    if(op instanceof SchemaVariable) {
		result.add((SchemaVariable)op);
	    }
	}
	
	return result;
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
     * @param declareSchemaVars
     *           Should declarations for the schema variables used in the taclet be pretty-printed?
     */
    public void printTaclet(Taclet taclet, 
	    		    SVInstantiations sv,
                            boolean showWholeTaclet,
                            boolean declareSchemaVars) {
	instantiations = sv;
	try {
	    Debug.log4jDebug(taclet.name().toString(),
		    	     LogicPrinter.class.getName());
	    if (showWholeTaclet) {
		layouter.beginC(2).print(taclet.name().toString()).print(" {");
	    } else {
		layouter.beginC();
	    }
	    if (declareSchemaVars) {
		Set<SchemaVariable> schemaVars = collectSchemaVars(taclet);
		layouter.brk();
		for(SchemaVariable schemaVar : schemaVars) {
                    layouter.print(schemaVar.proofToString() + "  ");
		}
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
	    Debug.log4jWarn("xxx exception occurred during printTaclet",
		    	    LogicPrinter.class.getName());
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
        // the last argument used to be false. Changed that - M.Ulbrich
        printTaclet(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, true, true); 
    }

    protected void printAttribs(Taclet taclet) throws IOException{
//        if (taclet.noninteractive()) {
//            layouter.brk().print("\\noninteractive");
//        }       
    }

    protected void printRewriteAttributes(RewriteTaclet taclet) throws IOException{
        final int applicationRestriction = taclet.getApplicationRestriction();
        if ((applicationRestriction & RewriteTaclet.SAME_UPDATE_LEVEL) != 0) {
            layouter.brk().print("\\sameUpdateLevel");
        }
        if ((applicationRestriction & RewriteTaclet.IN_SEQUENT_STATE) != 0) {
            layouter.brk().print("\\inSequentState");
        }
        if ((applicationRestriction & RewriteTaclet.ANTECEDENT_POLARITY) != 0) {
            layouter.brk().print("\\antecedentPolarity");
        }
        if ((applicationRestriction & RewriteTaclet.SUCCEDENT_POLARITY) != 0) {
            layouter.brk().print("\\succedentPolarity");
        }
    }

    protected void printVarCond(Taclet taclet) throws IOException{
        Iterator<NewVarcond> itVarsNew      = taclet.varsNew().iterator();
        Iterator<NewDependingOn> itVarsNewDepOn = taclet.varsNewDependingOn();
        Iterator<NotFreeIn> itVarsNotFreeIn = taclet.varsNotFreeIn();
        Iterator<VariableCondition> itVC = taclet.getVariableConditions();

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
            if(sv.getType() instanceof ArrayType) {
        	layouter.print(((ArrayType)sv.getType())
        		            .getAlternativeNameRepresentation());
            } else {
        	layouter.print(sv.getType().getFullName());
            }
        } else {
            layouter.print("\\typeof (").brk();
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
                for (Iterator<RuleSet> it = taclet.getRuleSets().iterator(); it.hasNext();) {
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

        for (final Iterator<TacletGoalTemplate> it =
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
		layouter.brk().beginC(2).print("\"" + tgt.name() + "\"").print(":");
	    }
			
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
	
	if (!(tgt.sequent().isEmpty())) {
	    printTextSequent(tgt.sequent(), "\\add", true);
	} 
	if (!tgt.rules().isEmpty()) {
	    printRules(tgt.rules());
	}
	if (tgt.addedProgVars().size()>0) {
	    layouter.brk();
	    printAddProgVars(tgt.addedProgVars());
	}
	
	if (tgt.name() != null) {
	    if (tgt.name().length() > 0) {
		layouter.brk(1,-2).end();
	    }
	}
	//layouter.end();
    }

    protected void printRules (ImmutableList<Taclet> rules) throws IOException{
        layouter.brk().beginC(2).print("\\addrules (");
        SVInstantiations svi = instantiations;
        for (Iterator<Taclet> it = rules.iterator(); it.hasNext();) {
            layouter.brk();
            Taclet t = it.next();
            printTaclet(t, instantiations, true, false);
            instantiations = svi;
        }
        layouter.brk(1,-2).print(")").end();
    }

    protected void printAddProgVars(ImmutableSet<SchemaVariable> apv) throws IOException {
        layouter.beginC(2).print("\\addprogvars (");
        for (Iterator<SchemaVariable> it = apv.iterator(); it.hasNext();) {
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
	    if (sv instanceof ProgramSV) {
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
		Debug.log4jWarn("Unknown instantiation type of " + o + 
			        "; class is " + o.getClass().getName(),
			        LogicPrinter.class.getName());
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
	Debug.log4jDebug("PP PV " + pv.name(), LogicPrinter.class.getName());
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
            ImmutableList<SequentPrintFilterEntry> antec = filter.getAntec();
            ImmutableList<SequentPrintFilterEntry> succ  = filter.getSucc();
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

    public void printSemisequent (ImmutableList<SequentPrintFilterEntry> p_formulas )
        throws IOException {
        Iterator<SequentPrintFilterEntry> it   = p_formulas.iterator ();
        SequentPrintFilterEntry           entry;
        int                               size = p_formulas.size     ();
        while ( size-- != 0 ) {
            entry = it.next ();
            markStartSub();
            printConstrainedFormula( entry.getFilteredFormula () );
            markEndSub();
            if ( size != 0 ) {
                layouter.print(",").brk(1);
            }
        }
    }

    /**
     * Pretty-prints a constrained formula. The constraint
     * "Constraint.BOTTOM" is suppressed
     *
     * @param cfma the constrained formula to be printed
     */
    public void printConstrainedFormula(SequentFormula cfma)
        throws IOException {
	printTerm(cfma.formula());
    }



    /**
     * Pretty-prints a term or formula.  How it is rendered depends on
     * the NotationInfo given to the constructor.
     *
     * @param t the Term to be printed
     */
    public void printTerm(Term t) throws IOException {
        if(notationInfo.getAbbrevMap().isEnabled(t)){
            startTerm(0);
            layouter.print(notationInfo.getAbbrevMap().getAbbrev(t));
        } else {
            if(t.hasLabels() && notationInfo.getNotation(t.op(), services).getPriority() < NotationInfo.PRIORITY_ATOM) {
                layouter.print("(");
            }
            notationInfo.getNotation(t.op(), services).print(t,this);
            if(t.hasLabels() && notationInfo.getNotation(t.op(), services).getPriority() < NotationInfo.PRIORITY_ATOM) {
                layouter.print(")");
            }
        }
        if (t.hasLabels()) {
            printLabels(t);
        }
    }

    public void printLabels(Term t) throws IOException {
        layouter.beginC().print("<<");
        boolean afterFirst = false;
        for (ITermLabel l : t.getLabels()) {
            if (afterFirst) {
               layouter.print(",").brk(1, 0);
            }
            else {
               afterFirst = true;
            }
            layouter.print(l.name().toString());
            if (l.getChildCount()>0) {
               layouter.print("(").beginC(2);
               for (int i = 0; i < l.getChildCount(); i++) {
                  layouter.print("\"" + l.getChild(i).toString() + "\"");
                  if (i < l.getChildCount() - 1) {
                     layouter.print(",").ind(1, 2);
                  }
               }
               layouter.end().print(")");
            }
        }
        layouter.end().print(">>");
    }

    /**
     * Pretty-prints a set of terms.
     * @param terms the terms to be printed
     */
    public void printTerm(ImmutableSet<Term> terms)
        throws IOException {
        getLayouter().print("{");
        Iterator<Term> it = terms.iterator();
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
    public void printTermContinuingBlock(Term t) throws IOException {
       if(t.hasLabels() && notationInfo.getNotation(t.op(), services).getPriority() < NotationInfo.PRIORITY_ATOM) {
           layouter.print("(");
       }
       notationInfo.getNotation(t.op(), services).printContinuingBlock(t,this);
       if(t.hasLabels() && notationInfo.getNotation(t.op(), services).getPriority() < NotationInfo.PRIORITY_ATOM) {
           layouter.print(")");
       }
       if (t.hasLabels()) {
          printLabels(t);
       }
    }


    /** Print a term in <code>f(t1,...tn)</code> style.  If the
     * operator has arity 0, no parentheses are printed, i.e.
     * <code>f</code> instead of <code>f()</code>.  If the term
     * doesn't fit on one line, <code>t2...tn</code> are aligned below
     * <code>t1</code>.
     *
     * @param name the name to be printed before the parentheses.
     * @param t the term to be printed.  */
    public void printFunctionTerm(String name, Term t) throws IOException {	
	//XXX
	if(NotationInfo.PRETTY_SYNTAX
           && services != null
           && t.op() instanceof Function
           && t.sort() == services.getTypeConverter().getHeapLDT().getFieldSort() 
           && t.arity() == 0
           && t.boundVars().isEmpty()) {
            startTerm(0);            
            final String prettyFieldName 
            	= services.getTypeConverter()
                          .getHeapLDT()
                          .getPrettyFieldName((Function)t.op());            
            layouter.print(prettyFieldName);
        } 
        
        else {
            startTerm(t.arity());
            layouter.print(name);
            if(!t.boundVars().isEmpty()) {
        	layouter.print("{").beginC(0);
        	printVariables(t.boundVars());
        	layouter.print("}").end();
            }
            if(t.arity() > 0) {
                layouter.print("(").beginC(0);
                for(int i = 0, n = t.arity(); i < n; i++) {
                    markStartSub();
                    printTerm(t.sub(i));
                    markEndSub();

                    if(i < n - 1) {
                        layouter.print(",").brk(1,0);
                    }
                }
                layouter.print(")").end();
            }
        }
    }

    public void printCast(String pre, 
	    		  String post,
	    		  Term t, 
	    		  int ass) throws IOException {
        final SortDependingFunction cast = (SortDependingFunction)t.op();
        
        startTerm(t.arity());
        layouter.print(pre);
        layouter.print(cast.getSortDependingOn().toString());
        layouter.print(post);
        maybeParens(t.sub(0), ass);
    }
    
    
    public void printSelect(Term t) throws IOException {
        assert t.boundVars().isEmpty();            
        assert t.arity() == 3;	
	final HeapLDT heapLDT = services == null 
			        ? null 
			        : services.getTypeConverter().getHeapLDT();
        if(NotationInfo.PRETTY_SYNTAX
            && heapLDT != null
            && t.sub(0).op().sort(t.subs()).equals(
               services.getNamespaces().sorts().lookup(new Name("Heap")))) {
            startTerm(3);
            
            final Term objectTerm = t.sub(1);
            final Term fieldTerm  = t.sub(2);
                
            final boolean printHeap = t.sub(0).op() != heapLDT.getHeap();
            if (printHeap) {
                markStartSub();
                printTerm(t.sub(0));
                markEndSub();
                layouter.print("[");
            } else {
                markStartSub();
            //heap not printed
            markEndSub();
            }

            if(objectTerm.equals(TermBuilder.DF.NULL(services))
                && fieldTerm.op() instanceof Function
                && ((Function)fieldTerm.op()).isUnique()) {
        	String className 
        		= heapLDT.getClassName((Function)fieldTerm.op());
        	
        	if(className == null) {
        	    markStartSub();
        	    printTerm(objectTerm);
        	    markEndSub();
        	} else {
        	    markStartSub();
        	    //"null" not printed
        	    markEndSub();
        	    layouter.print(className);
        	}
        	
        	layouter.print(".");
        	
                markStartSub();
                startTerm(0);                    
                printTerm(fieldTerm);
                markEndSub();                    
            } else if(fieldTerm.arity() == 0) {
        	markStartSub();
                printTerm(objectTerm);
                markEndSub();
        	
                layouter.print(".");
                
                markStartSub();
                startTerm(0);                    
                printTerm(fieldTerm);
                markEndSub();                    
            } else if(fieldTerm.op() == heapLDT.getArr()) {
        	markStartSub();
                printTerm(objectTerm);
                markEndSub();
        	
                layouter.print("[");
                
                markStartSub();
                startTerm(1);
                markStartSub();
                printTerm(fieldTerm.sub(0));
                markEndSub();
                markEndSub();
                
                layouter.print("]");
            } else {
        	printFunctionTerm(t.op().name().toString(), t);
            }	
            if (printHeap) {
                layouter.print("]");
            }
        } else {
            printFunctionTerm(t.op().name().toString(), t);
        }
    }
    
    
    public void printLength(Term t) throws IOException {
	final HeapLDT heapLDT = services == null 
        			? null 
        			: services.getTypeConverter().getHeapLDT();
	if(NotationInfo.PRETTY_SYNTAX && heapLDT != null) {
	    assert t.op() == heapLDT.getLength();
	    startTerm(t.arity());
	    
	    markStartSub();
	    printTerm(t.sub(0));
	    markEndSub();
	    layouter.print(".length");
	} else {
	    printFunctionTerm(t.op().name().toString(), t);            
	}	
    }
    
    
    public void printObserver(Term t) throws IOException {
	assert t.op() instanceof IObserverFunction;
	assert t.boundVars().isEmpty();
	final HeapLDT heapLDT = services == null 
			        ? null 
			        : services.getTypeConverter().getHeapLDT();	
	if(NotationInfo.PRETTY_SYNTAX
           && heapLDT != null 
           && t.sub(0).op().sort(t.subs()).equals(
                services.getNamespaces().sorts().lookup(new Name("Heap")))) {
	    final ObserverFunction obs = (ObserverFunction) t.op();
            startTerm(t.arity());

            final boolean printHeap = t.sub(0).op() != heapLDT.getHeap();
            if (printHeap) {
                markStartSub();
                printTerm(t.sub(0));
                markEndSub();
                layouter.print("[");
            } else {
                markStartSub();
            //heap not printed
            markEndSub();
            }
            
            if(!obs.isStatic()) {
        	markStartSub();
        	printTerm(t.sub(1));
        	markEndSub();
        	layouter.print(".");
            }
            
            final String prettyFieldName 
            	= services.getTypeConverter()
                          .getHeapLDT()
                          .getPrettyFieldName((Function)t.op());
            layouter.print(prettyFieldName);
            
            if(obs.getNumParams() > 0 || obs instanceof IProgramMethod) {
        	layouter.print("(").beginC(0);
        	for(int i = 0, n = obs.getNumParams(); i < n; i++) {
        	    markStartSub();
        	    printTerm(t.sub(i + (obs.isStatic() ? 1 : 2)));
        	    markEndSub();
                    if(i < n - 1) {
                        layouter.print(",").brk(1,0);
                    }
        	}
        	layouter.print(")").end();
            }
            if (printHeap) {
                layouter.print("]");
            }
        } else {
            printFunctionTerm(t.op().name().toString(), t);            
        }
    }
    
    
    public void printSingleton(Term t) throws IOException {
	assert t.arity() == 2;
	startTerm(2);	 
	layouter.print("{(").beginC(0);;

	markStartSub();	 
	printTerm(t.sub(0));
	markEndSub();
	
	layouter.print(",").brk(1,0);
	
	markStartSub();	 
	printTerm(t.sub(1));
	markEndSub();	

	layouter.print(")}").end();
    }  
    
    
    public void printElementOf(Term t) throws IOException {
	assert t.arity() == 3;
	startTerm(3);
	
	layouter.print("(").beginC(0);
	
	markStartSub();	 
	printTerm(t.sub(0));
	markEndSub();
	
	layouter.print(",").brk(1,0);
	
	markStartSub();	 
	printTerm(t.sub(1));
	markEndSub();

	layouter.print(")").end();
	layouter.print(" \\in ");
	
	markStartSub();	 
	printTerm(t.sub(2));
	markEndSub();	
    }     
    
    public void printElementOf(Term t, String symbol) throws IOException {
        if (symbol == null) {
            printElementOf(t);
            return;
        }

        assert t.arity() == 3;
        startTerm(3);
        
        layouter.print("(").beginC(0);
        
        markStartSub();  
        printTerm(t.sub(0));
        markEndSub();
        
        layouter.print(",").brk(1,0);
        
        markStartSub();  
        printTerm(t.sub(1));
        markEndSub();

        layouter.print(")").end();
        layouter.print(symbol);
        
        markStartSub();  
        printTerm(t.sub(2));
        markEndSub();   
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
     * Print a term with an update. This looks like
     * <code>{u} t</code>.  If line breaks are necessary, the
     * format is
     *
     * <pre>
     * {u}
     *   t
     * </pre>
     *
     * @param l       the left brace
     * @param r       the right brace
     * @param t       the update term
     * @param ass3    associativity for phi
     */
    public void printUpdateApplicationTerm (String l,
                                            String r,
                                            Term t,
                                            int ass3) throws IOException {
	assert t.op() instanceof UpdateApplication && t.arity() == 2;
		
	mark(MARK_START_UPDATE);
        layouter.beginC(2).print(l);
        startTerm(t.arity());
        
        markStartSub();
        printTerm(t.sub(0));
        markEndSub();        
        
        layouter.print(r);
        mark(MARK_END_UPDATE);
        layouter.brk(0);
        
        maybeParens(t.sub(1), ass3);
        
        layouter.end();
    }    
    
    
   /**
     * Print an elementary update.  This looks like
     * <code>loc := val</code>
     *
     * @param asgn    the assignment operator (including spaces)
     * @param ass2    associativity for the new values
     */
    public void printElementaryUpdate(String asgn,
                                      Term t,
                                      int ass2) throws IOException {
	ElementaryUpdate op = (ElementaryUpdate)t.op();
	
	assert t.arity() == 1;
	startTerm(1);
	
	layouter.print(op.lhs().name().toString());
	
	layouter.print(asgn);
	
	maybeParens(t.sub(0), ass2);
    }
    
    
    private void printParallelUpdateHelper(String separator, Term t, int ass)
    					    throws IOException {
	assert t.arity() == 2;
	startTerm(2);
	
	if(t.sub(0).op() == UpdateJunctor.PARALLEL_UPDATE) {
	    markStartSub();
	    printParallelUpdateHelper(separator, t.sub(0), ass);
	    markEndSub();
	} else {
	    maybeParens(t.sub(0), ass);
	}
	
	layouter.brk(1).print(separator + " ");
	
	if(t.sub(1).op() == UpdateJunctor.PARALLEL_UPDATE) {
	    markStartSub();
	    printParallelUpdateHelper(separator, t.sub(1), ass);
	    markEndSub();
	} else {
	    maybeParens(t.sub(1), ass);
	}	
    }
    
    
    public void printParallelUpdate(String separator, Term t, int ass) 
    					    throws IOException {
	layouter.beginC(0);
	printParallelUpdateHelper(separator, t, ass);
	layouter.end();
    }
    

    protected void printVariables (ImmutableArray<QuantifiableVariable> vars)
                                            throws IOException {
        int size = vars.size ();
        for(int j = 0; j != size; j++) {
            final QuantifiableVariable v = vars.get (j);
            if(v instanceof LogicVariable) {
                Term t =
                    TermFactory.DEFAULT.createTerm(v);
                if(notationInfo.getAbbrevMap().containsTerm(t)) {
                    layouter.print (v.sort().name().toString() + " " +
                                    notationInfo.getAbbrevMap().getAbbrev(t));
                } else {
                    layouter.print (v.sort().name() + " " + v.name ());
                }
            } else {
                layouter.print (v.name().toString());
            }
            if(j < size - 1) {
        	layouter.print(", ");
            }
        }
        layouter.print(";");        
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
        printVariables(new ImmutableArray<QuantifiableVariable>(v));
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
     * @param vars  the quantified variables (+colon and sort)
     * @param phi  the quantified formula
     * @param ass  associativity for phi
     */
    public void printQuantifierTerm(String name,
                                    ImmutableArray<QuantifiableVariable> vars,
                                    Term phi, 
                                    int ass)
        throws IOException {
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
	assert jb != null;
	assert jb.program() != null;
        if (phi.op() instanceof ModalOperatorSV) {
            Object o = getInstantiations().getInstantiation((ModalOperatorSV) phi.op());
            if (o == null) {
                Debug.log4jDebug("PMT  NO  " + phi + " @[ " + phi.op() + " ]@ " + " is : " +
                                   phi.getClass().getName() + " @[" + phi.op().getClass().getName() + "]@ known",
                                  LogicPrinter.class.getName());
            } else {
                //logger.debug("Instantiation of " + phi + " @[" + phi.op() + "]@" + " is : " + o + o.getClass().getName());
                //logger.debug(getInstantiations());
                Debug.log4jDebug("PMT YES " + phi.op() + " -> " + o
                                 + " @[" + o.getClass().getName() + "]@",
                                 LogicPrinter.class.getName());

                if(notationInfo.getAbbrevMap().isEnabled(phi)){
                    startTerm(0);
                    layouter.print(notationInfo.getAbbrevMap().getAbbrev(phi));
                } else {
                    Term[] ta = new Term[phi.arity()];
                    for (int i = 0; i < phi.arity(); i++) {
                        ta[i] = phi.sub(i);
                    }
                    Term term = TermFactory.DEFAULT.
			createTerm((Modality)o, ta, phi.boundVars(), phi.javaBlock());
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

    /**
     * returns the PositionTable representing position information on
     * the sequent of this LogicPrinter. Subclasses may overwrite
     * this method with a null returning body if position information
     * is not computed there.
     */
    public InitialPositionTable getInitialPositionTable() {
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
        throws IOException {
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
            mark(Integer.valueOf(size));
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
        prefixSort = t.sort();
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
    public static String escapeHTML(String text, boolean escapeWhitespace) {
         StringBuffer sb = new StringBuffer();
        
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
     * tests if the program name together with the prefix sort
     * determines the attribute in a unique way
     * @param programName the String denoting the program name of
     * the attribute
     * @param sort the ObjectSort specifying the hierarchy
     * where to test for uniqueness
     * @param services the Services class used to access the type hierarchy
     * @return true if the attribute is uniquely determined
     */
    public static boolean printInShortForm(String programName, 
	    				   Sort sort,
	    				   Services services) {
        if ( ! ( services != null  
        	  && sort.extendsTrans(services.getJavaInfo().objectSort()))) {
            return false;
        }
        final KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
        assert kjt != null : "Did not find KeYJavaType for " + sort;
        return 
            services.getJavaInfo().getAllAttributes(programName, kjt).size() == 1;
    }

    /** Utility class for stack entries containing the position table
     * and the position of the start of the subterm in the result.  */
    private static class StackEntry {

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
    private static class PosTableStringBackend extends StringBackend {

        /** The top PositionTable */
        private final InitialPositionTable initPosTbl 
        	= new InitialPositionTable();

        /** The resulting position table or an intermediate result */
        private  PositionTable posTbl = initPosTbl;

        /** The position in result where the current subterm starts */
        private int pos = 0;

        /** The stack of StackEntry representing the nodes above
         * the current subterm */
        private final Stack<StackEntry> stack = new Stack<StackEntry>();

        /** If this is set, a ModalityPositionTable will
         * be built next.
         */
        private boolean need_modPosTable = false;

        /** These two remember the range corresponding to the first
         * executable statement in a JavaBlock */
        private int firstStmtStart;
        private Range firstStmtRange;

        /** Remembers the start of an update to create a range */
        private final Stack<Integer> updateStarts = new Stack<Integer>();
        

        PosTableStringBackend(int lineWidth) {
            super(lineWidth);
        }

        /** Returns the constructed position table.
         *  @return the constructed position table
         */
        public InitialPositionTable getPositionTable() {
            return initPosTbl;
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
                StackEntry se=stack.peek();
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
        	updateStarts.push(count());
            } else if ( o==MARK_END_UPDATE ) {
        	int updateStart = updateStarts.pop();
                initPosTbl.addUpdateRange(new Range(updateStart, count()));
            }
        }
    }
}
