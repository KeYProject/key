package de.uka.ilkd.hoare.pp;

import java.io.IOException;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.util.pp.Backend;
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

    private static final String SEMI_SEQ_SEP_ANTEC = " & ";
    private static final String SEMI_SEQ_SEP_SUCC = " | ";
    private boolean previousPrintedOpWasQuanUpdate;

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter, NotationInfo notationInfo, Backend backend, Services services, boolean purePrint) {
        super(prgPrinter, notationInfo, backend, services, purePrint);
        tweakNotationInfo(notationInfo, services);
    }

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter, NotationInfo notationInfo, Services services, boolean purePrint) {
        super(prgPrinter, notationInfo, services, purePrint);
        tweakNotationInfo(notationInfo, services);
    }

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter, NotationInfo notationInfo, Services services) {
        super(prgPrinter, notationInfo, services);
        tweakNotationInfo(notationInfo, services);
    }

    public HoareLogicPrettyPrinter(ProgramPrinter prgPrinter, 
            NotationInfo notationInfo, Backend backend, Services services) {
        super(prgPrinter, notationInfo, backend, services);       
        tweakNotationInfo(notationInfo, services);
    }

    private void tweakNotationInfo(NotationInfo notInfo, Services services) {        
        if (services == null) return;
        PresentationFeatures.putPrefixNotation(notInfo, services.getNamespaces().functions(), "javaUnaryMinusInt" , "-");
        PresentationFeatures.putPrefixNotation(notInfo, services.getNamespaces().functions(), "javaUnaryMinusLong", "-");
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaAddInt" , "+", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaAddLong", "+", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaSubInt" , "-", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaSubLong", "-", 90, 90, 91);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaMulInt" , "*", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaMulLong", "*", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaDivInt" , "/", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaDivLong", "/", 100, 100, 101);
        PresentationFeatures.putInfixNotation(notInfo, services.getNamespaces().functions(), "javaMod" , "%", 100, 100, 101);
    
        notInfo.put(QuanUpdateOperator.class, new QuanUpdate());
    }
    
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
                    sp.printQuanUpdateTerm("[", ":=", "]", t, 80, 0, assTarget);
                }
            }
        }
    }
    
    public void printSequent(SequentPrintFilter filter,
            boolean finalbreak) {
        printSequent(filter.getSequent());
    }
    
    
    public void printSequent(Sequent seq, boolean finalbreak) {        
        final Semisequent succ  = seq.succedent();        
        final int idx = findProgramFormula(succ.iterator());        
        if (idx >= 0) {        
            markStartSub();
            printSequentAsHoareTriple(seq, finalbreak,idx);
            markEndSub();
        } else {
            printNormalSequent(seq, finalbreak);
        }                          
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
        layouter.beginC ( 2 );
        if (!previousPrintedOpWasQuanUpdate) {
            layouter.print ( l );
            previousPrintedOpWasQuanUpdate = false;
        }
        startTerm ( t.arity () );
        for ( int i = 0; i < op.locationCount (); i++ ) {
            final Operator loc = op.location ( i );

            layouter.beginC(0);
            printUpdateQuantification ( t, op, i );

            final String[] separator = setupUpdateSeparators ( loc,
                                                               op.location(t, i));
            for ( int j = loc.arity (); j >= 1; j-- ) {
                final Term sub = t.sub ( op.valuePos ( i ) - j );

                markStartSub ();
                printTerm ( sub );
                markEndSub ();
                layouter.print ( separator[loc.arity () - j] );
            }
            layouter.print ( asgn ).brk(0,0);
            layouter.end();
            maybeParens ( op.value ( t, i ), ass2 );
            if ( i < op.locationCount () - 1 ) {
                layouter.print ( " ||" ).brk ( 1, 0 );
            }
        }

        if (op.target(t).op() instanceof QuanUpdateOperator) {
            layouter.print(",").brk(1);
            previousPrintedOpWasQuanUpdate = true;
        } else {
            layouter.print ( r ).brk ( 0 );
        }
        maybeParens ( op.target(t), ass3 );
        layouter.end ();
    }

    
    public void printNormalSequent(Sequent seq,
            boolean finalbreak) {
        try {
            Semisequent antec = seq.antecedent();
            Semisequent succ  = seq.succedent();
            markStartSub();
            startTerm(antec.size()+succ.size());
            layouter.beginC(0).ind();
            layouter.print("|-").brk(1,2);
            
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
                    printSemisequent(succ.remove(idx).semisequent(), false, true);                
                }
                if (formulaInAntec) layouter.brk(1,-1).print("->").brk(1,2);
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
            throw new RuntimeException ("IO Exception in pretty printer:\n"+e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException (
                    "Unbalanced blocks in pretty printer:\n"+e);
        }
    }

    
    private void printSequentAsHoareTriple(Sequent seq,
            boolean finalbreak, int idx) {
        try {
            final Semisequent antec = seq.antecedent();
            final Semisequent succ  = seq.succedent();

            startTerm( antec.size() + succ.size() );

            layouter.beginC(0).print("{");
            
            layouter.beginC(1).ind(1,1);
            printSemisequent(antec, true, false);
            if (antec.size() > 0) {
                if (succ.size() > 1) {
                    layouter.print(SEMI_SEQ_SEP_ANTEC).brk(1);
                }            
            }

            printSemisequent( succ.remove(idx).semisequent(), false, true);
            layouter.brk(1).print("}").end();

            layouter.brk();

       
            markStartSub(); // start program formula
            printProgramFormula(idx, succ);
            markEndSub(); //end program formula
        } catch (IOException e) {
            throw new RuntimeException ("IO Exception in pretty printer:\n"+e);
        } catch (UnbalancedBlocksException e) {
            throw new RuntimeException (
                    "Unbalanced blocks in pretty printer:\n"+e);
        }
    }

    private void printProgramFormula(int idx, final Semisequent succ) throws IOException {
        Term programFormula = succ.get(idx).formula(); 
             
        layouter.brk();
        
        layouter.beginC(0).print("[");
        int count = 0;
        while (programFormula.op() instanceof QuanUpdateOperator) {
            startTerm(programFormula.arity());
            printQuanPrefix(programFormula);
            programFormula = ((QuanUpdateOperator)programFormula.op()).target(programFormula);
            count ++;
            if (!(programFormula.op() instanceof Modality)) {
                layouter.print(", ");
                markStartSub();
            }  
        }
        layouter.print("]").end().brk();
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


        for (int i = 0; i<count; i++) {
            markEndSub();
        }                       
                    

        layouter.end();
    }

    public void printCast(String pre, String post,
            Term t, int ass) throws IOException {
        startTerm(t.arity());
        //markStartSub();
        maybeParens(t.sub(0), ass);
        //printTerm(t.sub(0));
        //markEndSub();
    }
        
    private void printQuanPrefix(Term term) throws IOException {              
        Term t = term;
        final QuanUpdateOperator op = (QuanUpdateOperator)t.op ();
        layouter.beginC ( 2 );
        for ( int i = 0; i < op.locationCount (); i++ ) {
            final Operator loc = op.location ( i );

            layouter.beginC(0);
            printUpdateQuantification ( t, op, i );

            final String[] separator = setupUpdateSeparators ( loc,
                    op.location(t, i));
            for ( int j = loc.arity (); j >= 1; j-- ) {
                final Term sub = t.sub ( op.valuePos ( i ) - j );
                markStartSub ();
                printTerm ( sub );
                markEndSub ();
                layouter.print ( separator[loc.arity () - j] );

            }
            layouter.print ( ":=" ).brk(0,0);
            layouter.end();
            maybeParens ( op.value ( t, i ), 0 );
            if ( i < op.locationCount () - 1 ) {
                layouter.print ( " ||" ).brk ( 1, 0 );
            }
        }
        layouter.end();
    }
    

    /** returns the index of the first formula containing a program or <tt>-1</tt>
     * if no such formula exists
     * @param semi the Semisequent to search through
     * @return the index of the formula containing a program or <tt>-1</tt>
     */
    private int findProgramFormula(IteratorOfConstrainedFormula it) {       
        int idx = 0;        
           
        while (it.hasNext()) {
            final ConstrainedFormula cf = it.next();
            if (hasProgram(cf.formula())) {
                return idx;
            }
            idx ++;
        }
        return -1;
    }

    /** returns the index of the first formula containing an update on top level 
     * or <tt>-1</tt> if no such formula exists
     * @param semi the Semisequent to search through
     * @return the index of the formula containing an update or <tt>-1</tt>
     */
    private int findUpdateFormula(IteratorOfConstrainedFormula it) {       
        int idx = 0;        
           
        while (it.hasNext()) {
            final ConstrainedFormula cf = it.next();
            if (cf.formula().op() instanceof QuanUpdateOperator) {
                return idx;
            }
            idx ++;
        }
        return -1;
    }

    
    /**
     * Print a Java block.  This is formatted using the ProgramPrinter
     * given to the constructor.  The result is indented according to
     * the surrounding material.  The first `executable' statement is
     * marked for highlighting.
     *
     * @param j the Java block to be printed
     */
    public void printHoareProgramBlock(JavaBlock j)
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
        String s = sw.toString().replaceFirst("\\{", " ");
        s = s.substring(0, s.lastIndexOf('}'))+" ";
        printMarkingFirstStatement(s,r);
    }

    /**
     * returns if a formula contains a program. Attention: the implementation 
     * makes heavy usage of the assumptions stated in the class comment
     * @param formula
     * @return
     */
    private boolean hasProgram(Term formula) {
        if (formula.sort() != Sort.FORMULA) {
            return false;
        } else if (formula.op() instanceof Modality) {
            return true;
        }
        assert !(formula.op() instanceof Modality) : "Hoare Tuple Normalform hurt.";

        if (formula.op() instanceof QuanUpdateOperator) {
            return hasProgram(((QuanUpdateOperator)formula.op()).target(formula));
        }
        
        return false;
    }

    
    /**
     * Pretty-prints a Semisequent.  Formulae are separated by commas.
     *
     * @param semiseq the semisequent to be printed
     */
    public void printSemisequent(Semisequent semiseq, boolean antec)
        throws IOException
    {
        printSemisequent(semiseq, antec, !antec);
    }
    
    /**
     * Pretty-prints a Semisequent.  Formulae are separated by commas.
     *
     * @param semiseq the semisequent to be printed
     */
    public void printSemisequent(Semisequent semiseq, boolean antec, boolean succ2antec)
        throws IOException
    {
        for (int i=0;i<semiseq.size();i++) {
            markStartSub();
            if (succ2antec) layouter.print("!(");
            printConstrainedFormula(semiseq.get(i));
            if (succ2antec) layouter.print(")");
            markEndSub();
            if (i!=semiseq.size() - 1) {                
                if (succ2antec || antec) { 
                    layouter.print(SEMI_SEQ_SEP_ANTEC).brk(1);
                } else {
                    layouter.print(SEMI_SEQ_SEP_SUCC).brk(1);                    
                }
            }
        }
    }

    public void printSemisequent (ListOfSequentPrintFilterEntry p_formulas, boolean antec)
    throws IOException {
        printSemisequent(p_formulas, antec, !antec);
    }

    public void printSemisequent (ListOfSequentPrintFilterEntry p_formulas, boolean antec, boolean succ2antec)
    throws IOException {

        IteratorOfSequentPrintFilterEntry it   = p_formulas.iterator ();
        SequentPrintFilterEntry           entry;
        int                               size = p_formulas.size     ();
        while ( size-- != 0 ) {
            entry = it.next ();
            markStartSub();
            formulaConstraint = entry.getDisplayConstraint ();
            if (succ2antec) layouter.print("!(");
            printConstrainedFormula( entry.getFilteredFormula () );
            if (succ2antec) layouter.print(")");  
            markEndSub();
            if ( size != 0 ) {
                if (succ2antec || antec) { 
                    layouter.print(SEMI_SEQ_SEP_ANTEC).brk(1);
                } else {
                    layouter.print(SEMI_SEQ_SEP_SUCC).brk(1);                    
                }
            }
        }
        formulaConstraint = null;
    }
 
    
    
}
