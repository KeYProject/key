// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof.decproc;


import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.smt.ConstraintSet;
import de.uka.ilkd.key.smt.NumberTranslation;
import de.uka.ilkd.key.util.Debug;


public class ICSTranslation extends DecProcTranslation{ //public since asmkey needs it (or will need it ...)

    private HashMap cacheForUninterpretedSymbols = null;

    /**
     * Just a constructor which starts the conversion to Simplify syntax.
     * The result can be fetched with @see getText-
     * @param sequent The sequent which shall be translated.
     * @param cs The constraints which shall be incorporated.
     * @param localmv The local metavariables, should be the ones introduced
     *    after the last branch.
     */
    public ICSTranslation(Sequent sequent, ConstraintSet cs, 
			  SetOfMetavariable localmv, Services services) throws SimplifyException  {
    	super(sequent, cs, localmv, services);
	cacheForUninterpretedSymbols = new HashMap();
    	StringBuffer sb = translate(sequent);
    	sb.insert(0,signatures);
    	text = sb.toString();
		if (notes.length() > 0) {
			logger.info(notes);
		}
	}
    
    /**
     * Goes through the collected metavariables and quantifies them with 
     * universal-quantifieres if they are global and with existential 
     * quantifiers if they are local.
     * This method is completely useless at the moment since ICS cannot handle 
     * quantifiers yet.
     * @param s The StringBuffer the quantifieres shall be pre- and 
     * the trailing parantheses be appended.
     * @returns The modified StringBuffer as a String.
     */
    protected final String produceClosure(StringBuffer s) {
	StringBuffer tmp = new StringBuffer("(");
	tmp.append(DecisionProcedureICSOp.ALL)
	    .append(" (");
	for (Iterator i = usedGlobalMv.iterator(); i.hasNext();){
	    tmp.append(' ')
		.append(getUniqueVariableName((Metavariable)i.next()));
	}
	tmp.append(")");

	tmp.append("(")
	    .append(DecisionProcedureICSOp.EX)
	    .append(" (");
	for (Iterator i = usedLocalMv.iterator(); i.hasNext(); ) {
	    tmp.append(' ')
		.append(getUniqueVariableName((Metavariable)i.next()));
	}
	tmp.append(") ");

	tmp.append(s);

	tmp.append(" ))");

	return tmp.toString();
    }

    /** Translates the given sequent into "ICS" input syntax 
     *
     * @param sequent the Sequent which should be written in ICS syntax
     * @return the translated version of s
     */
    protected final StringBuffer translate(Sequent sequent) throws SimplifyException  {
	//    	computeModuloConstraints(sequent);
	StringBuffer sb = new StringBuffer();
	sb.append("sat ").append(DecisionProcedureICSOp.NOT).append('[');
	sb.append('[');
	StringBuffer hb = translate(sequent.antecedent(), ANTECEDENT);
	if (hb.length() > 0) {
	    sb.append(hb);
	} else {
	    sb.append(DecisionProcedureICSOp.TRUE);
	}
// 	Term Tt = Moduloconjoin();
// 	Constrainedformula Ccff = New Constrainedformula(Tt); 
// 	Hb = Translate(Ccff,	Antecedent, True);
// 	If (Hb.Length() > 0) {
// 	    Sb.Append(Decisionprocedureicsop.And).Append(' ');
// 	    Sb.Append(Hb);
// 	}
	sb.append(']');
	sb.append("\n").append(DecisionProcedureICSOp.IMP).append("\n");
	hb = translate(sequent.succedent(), SUCCEDENT);
	if (hb.length() > 0) {
	    sb.append(hb);
	} else {
	    sb.append(DecisionProcedureICSOp.FALSE);
	}
	sb.append("].");
	return sb;
    }

    /** Translates the given Semisequent into "ICS" input syntax
     * and returns the resulting StringBuffer sb.
     *
     * @param ss the SemiSequent which should be written in ICS syntax
     * @param skolemization Indicates whether the formula is in the ANTECEDENT, 
     *        SUCCEDENT or with YESNOT if a "not" operation occurres above the 
     *        term which will prevent skolemization ("not"s are not counted).
     */
    protected final StringBuffer translate(Semisequent ss, int skolemization)
			throws SimplifyException {
		StringBuffer sb = new StringBuffer();
		StringBuffer hb = new StringBuffer();
		char lop;
		StringBuffer undef;
		if (skolemization == ANTECEDENT) {
			lop = '&';
			undef = new StringBuffer(DecisionProcedureICSOp.TRUE);
		} else {
			lop = '|';
			undef = new StringBuffer(DecisionProcedureICSOp.FALSE);
		}
		for (int i = 0; i < ss.size(); ++i) {
			hb = translate(ss.get(i), skolemization, false);
			if (i > 0) {
				sb.append(lop).append(' ');
			}
			if (hb.length() > 0) {
				sb.append(hb);
			} else {
				sb.append(undef);
			}
		}
		return sb;
    }

    /**
	 * Translates the given ConstrainedFormula into "ICS" input and returns the
	 * resulting StringBuffer sb.
	 * 
	 * @param cf
	 *           the ConstrainedFormula which should be written in ICS syntax
	 * @param skolemization
	 *           Indicates whether the formula is in the ANTECEDENT, SUCCEDENT
	 *           or with YESNOT if a "not" operation occurres above the term
	 *           which will prevent skolemization ("not"s are not counted).
	 * @param overWriteUsed
	 *           the ConstrainedFormulas generated in the modulo replacement
	 *           process are not "used" elsewhere. This can be compensated with
	 *           this flag.
	 */
    protected final StringBuffer translate(ConstrainedFormula cf, int skolemization, boolean overWriteUsed)
	    throws SimplifyException {
	StringBuffer sb = new StringBuffer();
	if (constraintSet.used(cf) | overWriteUsed) {
	    SyntacticalReplaceVisitor srVisitor =
		new SyntacticalReplaceVisitor(constraintSet.chosenConstraint());
	    cf.formula().execPostOrder ( srVisitor );
	    sb.append(translate(srVisitor.getTerm(), skolemization, new Vector()));
	}
	//sb.append(translate(cf.formula()));
	return sb;
    }

    /**
	 * Translates the given term into "ICS" input syntax and and returns
	 * the resulting StringBuffer sb.
	 * 
	 * @param term
	 *           the Term which should be written in Simplify syntax
	 * @param skolemization
	 *           Indicates whether the formula is in the ANTECEDENT, SUCCEDENT
	 *           or with YESNOT if a "not" operation occurres above the term
	 *           which will prevent skolemization ("not"s are not counted).
	 * @param quantifiedVars
	 *           a Vector containing all variables that have been bound in
	 *           super-terms. It is only used for the translation of modulo
	 *           terms, but must be looped through until we get there.
	 */
    protected final StringBuffer translate(Term term, int skolemization, Vector quantifiedVars) 
	    throws SimplifyException {
	Operator op = term.op();
// 	System.out.println("sort=" + term.sort().name() 
// 			   + ", opName=" + term.op().name()
// 			   + ", opClass=" + term.op().getClass().getName()
// 			   + ", arity=" + term.arity());

	if (op == Op.NOT) {
	    return(translatePrefixTerm(term, DecisionProcedureICSOp.NOT,
					BOOLEAN, YESNOT, quantifiedVars));
	} else if (op == Op.AND) {
	    return(translateBinaryInfixTerm(term, DecisionProcedureICSOp.AND,
					    BOOLEAN, skolemization, quantifiedVars));
	} else if (op == Op.OR) {
	    return(translateBinaryInfixTerm(term, DecisionProcedureICSOp.OR, 
					    BOOLEAN, skolemization, quantifiedVars));
	} else if (op == Op.IMP) {
	    return(translateBinaryInfixTerm(term, DecisionProcedureICSOp.IMP, 
					    BOOLEAN, YESNOT, quantifiedVars));
	} else if (op == Op.EQV) {
	    return(translateBinaryInfixTerm(term, DecisionProcedureICSOp.EQV, 
					    BOOLEAN, YESNOT, quantifiedVars));
	} else if (op == Op.EQUALS) {
	    if (term.sub(0).sort() == term.sub(0).sort()
		&& term.sub(0).sort() == services.getTypeConverter().getIntegerLDT().targetSort())
		return(translateBinaryInfixTerm(term, DecisionProcedureICSOp.EQUALS
						, BOOLEAN, skolemization, quantifiedVars));
	    else
		return uninterpretedTerm(term, true);
	} else if ((op == Op.EX) & (skolemization == ANTECEDENT)) {
	    Debug.assertTrue(term.arity() == 1);
		Vector cloneVars = (Vector)quantifiedVars.clone(); 
		collectQuantifiedVars(cloneVars, term);
	    return(translate(term.sub(0), skolemization, cloneVars));
	} else if ((op == Op.ALL) & (skolemization == SUCCEDENT)) {
	    Debug.assertTrue(term.arity() == 1);
		Vector cloneVars = (Vector)quantifiedVars.clone(); 
		collectQuantifiedVars(cloneVars, term);
	    return(translate(term.sub(0), skolemization, cloneVars));
	} else if (op == Op.TRUE) {
	    return(new StringBuffer(DecisionProcedureICSOp.TRUE));
	} else if (op == Op.FALSE) {
	    return(new StringBuffer(DecisionProcedureICSOp.FALSE));
	} else if (op instanceof AttributeOp) {
	    return(translateAttributeOpTerm(term, skolemization, quantifiedVars));
	} else if (op instanceof ProgramMethod) {
	    return(translatePrefixTerm(term, 
					getUniqueVariableName(op).toString(),
					FUNCTION, skolemization, quantifiedVars));
	} else if (op instanceof LogicVariable||op instanceof ProgramVariable){
	    return(translateVariable(op));
	} else if (op instanceof Metavariable) {
	    //	    System.out.println("Metavariable" + op);
	    if (localMetavariables.contains((Metavariable)op)) {
		usedLocalMv.add(op);
	    } else {
		usedGlobalMv.add(op);
	    }
	    return(translateVariable(op));
	} else if (op instanceof ArrayOp) {
	    return new StringBuffer(translate(term.sub(0), skolemization, quantifiedVars)+"["+
				    translate(term.sub(1), skolemization, quantifiedVars)+"]");
	} else if (op instanceof Function) {
	    String name = op.name().toString().intern();
	    if (name.equals("add")) {
		return(translateBinaryInfixTerm(term, 
						DecisionProcedureICSOp.PLUS,
						FUNCTION, skolemization, quantifiedVars));
	    } else if (name.equals("sub"))  {
		return(translateBinaryInfixTerm(term, 
						DecisionProcedureICSOp.MINUS, 
						FUNCTION, skolemization, quantifiedVars));
	    } else if (name.equals("neg")) {
		return(translatePrefixTerm(term, DecisionProcedureICSOp.MINUS, 
					    FUNCTION, skolemization, quantifiedVars));
	    } else if (name.equals("mul")) {
		return(translateBinaryInfixTerm(term, 
						DecisionProcedureICSOp.MULT, 
						FUNCTION, skolemization, quantifiedVars));
	    } else if (name.equals("div")) {
		notes.append("Division encountered (not supported by ICS).");
		//System.out
		//.println("Division encountered (not supported by ICS).");
		return(translatePrefixTerm(term, 
					  getUniqueVariableName(op).toString(),
					  FUNCTION, skolemization, quantifiedVars));
// 		} else if (name.equals("mod")) {
// 			Term tt = translateModulo(term, quantifiedVars);
// 			if (tt == null) {
// 				return (translatePrefixTerm(
// 					    term, getUniqueVariableName(op).toString(), FUNCTION, 
// 					    skolemization, quantifiedVars));
// 			} else {
// 				return translate(tt, skolemization, quantifiedVars);
// 			}

	    } else if (name.equals("lt")) {
		return(translateBinaryInfixTerm(term, DecisionProcedureICSOp.LT
						, BOOLEAN, skolemization, quantifiedVars));
	    } else if (name.equals("gt")) {
		return(translateBinaryInfixTerm(term, DecisionProcedureICSOp.GT
						, BOOLEAN, skolemization, quantifiedVars));
	    } else if (name.equals("leq")) {
		return(translateBinaryInfixTerm(term, 
						DecisionProcedureICSOp.LEQ, 
						BOOLEAN, skolemization, quantifiedVars));
	    } else if (name.equals("geq")) {
		return(translateBinaryInfixTerm(term, 
						DecisionProcedureICSOp.GEQ, 
						BOOLEAN, skolemization, quantifiedVars));
	    } else if (name.equals("Z") || 
		       name.equals("C")) {
		Debug.assertTrue(term.arity() == 1);
		return(new StringBuffer((NumberTranslation.translate(
					   term.sub(0))).toString()));
	    } else if (name.equals("byte_MIN") 
		    | name.equals("byte_MAX")
		    | name.equals("byte_RANGE") 
		    | name.equals("byte_HALFRANGE")
		    | name.equals("short_MIN") 
		    | name.equals("short_MAX")
		    | name.equals("short_RANGE") 
		    | name.equals("short_HALFRANGE")
		    | name.equals("int_MIN") 
		    | name.equals("int_MAX")
		    | name.equals("int_RANGE") 
		    | name.equals("int_HALFRANGE")
		    | name.equals("long_MIN") 
		    | name.equals("long_MAX")
		    | name.equals("long_RANGE") 
		    | name.equals("long_HALFRANGE") ) {
		return(new StringBuffer(translateLimitTerm(name)));
	    } else {
		if (term.sort() == Sort.FORMULA) {
		    addPredicate(getUniqueVariableName(op).toString(),
				op.arity());
		    return(translatePrefixTerm(
			term, getUniqueVariableName(op).toString(), PREDICATE, 
			skolemization, quantifiedVars));
		}
		return(translatePrefixTerm(
		    term, getUniqueVariableName(op).toString(), FUNCTION, 
		    skolemization, quantifiedVars));
	    }
	} else if ((op instanceof Modality) || 
		   (op instanceof IUpdateOperator )) {
	    return(uninterpretedTerm(term, true));
	} else {
		return translateUnknown(term, skolemization);
	}
    }

    /**
     * Takes care of sequent tree parts that were not matched in
     * translate(term, skolemization).
     * In this class it just produces a warning, nothing more.
     * It is provided as a hook for subclasses. 
     * @param term The Term given to translate
     * @param skolemization dto.
     * @return new StringBuffer();
     * @throws SimplifyException
     */
    protected StringBuffer translateUnknown(Term term, int skolemization) 
    throws SimplifyException {
	    logger.warn("Warning: unknown operator while translating into ICS "
				+"syntax. Translation to ICS will be stopped here.\n"
				+ "opClass=" + term.op().getClass().getName()
				+ ", opName=" + term.op().name()
				+ ", sort=" + term.sort().name());
		    //throw new SimplifyException(op.name() + " not known by ICS");
		    
		return new StringBuffer();
    	
    }

    
    /** 
     * 
     * @param name The name of the term
     */
    protected final String translateLimitTerm(String name) {
	if (name.equals("byte_MIN")) {
		return("-128");
	    } else if (name.equals("byte_MAX")) {
		return("127");
	    } else if (name.equals("byte_RANGE")) {
		return("256");		
	    } else if (name.equals("byte_HALFRANGE")){
		return("128");
	    } else if (name.equals("short_MIN")) {
		return("-32768");
	    } else if (name.equals("short_MAX")) {
		return("32767");
	    } else if (name.equals("short_RANGE")) {
		return("65536");
	    } else if (name.equals("short_HALFRANGE")) {
		return("32768");
	    } else if (name.equals("int_MIN")) {
		return("-2147483648");
	    } else if (name.equals("int_MAX")) {
		return("2147483647");
	    } else if (name.equals("int_RANGE")) {
		return("4294967296");
	    } else if (name.equals("int_HALFRANGE")) {
		return("2147483648");
	    } else if (name.equals("long_MIN")) {
		return("-9223372036854775808");
	    } else if (name.equals("long_MAX")) {
		return("9223372036854775807");
	    } else if (name.equals("long_RANGE")) {
		return("18446744073709551616");
	    } else if (name.equals("long_HALFRANGE")) {
		return("9223372036854775808");
	} else {
	    return "";
	}
    }
    /** 
     * Used to give a variable (program, logic, meta) a unique name.
     * @param op The variable to be translated/renamed.
     */
    protected final StringBuffer translateVariable(Operator op) {
		StringBuffer hb = getUniqueVariableName(op);
		if (!sigTable.contains(op)) {
			signatures.append("sig ").append(hb).append(":int.\n");
			sigTable.add(op);
		}
		return hb;
	}

    /**
	 * produces a unique name for the given Variable, with a unique hashcode and
	 * without characters ICS does not understand
	 * 
	 * @param op
	 *           The variable to get a new name.
	 */
    protected final StringBuffer getUniqueVariableName(Operator op) {
	StringBuffer sb = new StringBuffer(op.name().toString());
	//logger.debug("sb == " + sb);
	char c;
	if (sb.charAt(0) == '_') {
	    sb.replace(0,1,"UNDERSCORE_");
	}
	if (sb.charAt(0) == '$') {
	    sb.replace(0,1,"DOLLAR_");
	}
	if (sb.charAt(0) == '.') {
	    sb.deleteCharAt(0);
	}
	if (sb.charAt(0) == '@') {
	    sb.replace(0,1,"AT_");
	}
	for (int i = 0; i < sb.length(); i++) {	
	    c = sb.charAt(i);
	    if (c == '$') {
		sb.replace(i,i,"_DOLLAR_");
	    } else if (c == '@') {
		sb.replace(i,i+1,"_AT_");
		//logger.debug("@");
	    } else if ((i < sb.length() - 1) && (sb.substring(i, i+2).equals("::"))) {
		sb.replace(i,i+2,"__");
		//logger.debug("::");
	    } else if (! (Character.isLetterOrDigit(c) | c == '_')) {
		sb.deleteCharAt(i);
		//logger.debug("~");
	    }
	}
	if (sb.length() == 0) {
	    sb.append("DummyName");
	}
	sb.append('_').append(getUniqueHashCode(op));
	return sb;
    }
    
    /**
	 * Takes a term which is ICS not capable of handling. This term is
	 * translated into a predicate.
	 * 
	 * @param term
	 *           the Term ICS cannot handle directly
	 * @param modRenaming
	 *           true iff equality should be modulo renaming or not. This will
	 *           result in the same names, if just the free variables are
	 *           different, but the rest isn't.
	 * @return the StringBuffer with the translation of an uninterpreted term
	 */
    protected final StringBuffer uninterpretedTerm(Term term, boolean modRenaming) {
	if (cacheForUninterpretedSymbols.containsKey(term))
	    return (StringBuffer)cacheForUninterpretedSymbols.get(term);
	StringBuffer sb = new StringBuffer();
	StringBuffer temp = new StringBuffer().append('[');
	temp.append(term.op().name())
	    .append('_');
	if (modRenaming) {
	    temp.append(getUniqueHashCodeForUninterpretedTerm(term));
	} else {
	    temp.append(getUniqueHashCode(term));
	}
	sb.append(temp).append('(');
	IteratorOfQuantifiableVariable i;
	int round = 0;
	for ( i = term.freeVars().iterator(); i.hasNext(); ) {
	    if (round++ > 0) {
		sb.append(", ");
	    }
	    sb.append(' ');
	    sb.append(translateVariable(i.next()));
	}
	sb.append(')').append(DecisionProcedureICSOp.EQUALS)
	    .append(TRUEVAL).append(']');
	if (term.sort() == Sort.FORMULA)
	    addPredicate(temp.toString(), term.freeVars().size());
	cacheForUninterpretedSymbols.put(term, sb);
	return sb;
    }

    /**
	 * Takes a prefix-term and translates it with its arguments into the ICS
	 * syntax. Examples are x, f(x), f(x, y)
	 * 
	 * @param term
	 *           The term to be converted.
	 * @param name
	 *           The name that should be used for the term (should be unique,
	 *           it should be taken care of that somewhere else (if desired)).
	 * @param brackets
	 *           logical terms can (and should) be put into brackets (if they
	 *           are composite), function terms into rounded parantheses;
	 *           indicate that with one of NONE, BOOLEAN, FUNCTION or PREDICATE
	 * @param skolemization
	 *           Indicates whether the formula is in the ANTECEDENT, SUCCEDENT
	 *           or with YESNOT if a "not" operation occurres above the term
	 *           which will prevent skolemization ("not"s are not counted).
	 * @param quantifiedVars
	 *           a Vector containing all variables that have been bound in
	 *           super-terms. It is only used for the translation of modulo
	 *           terms, but must be looped through until we get there
	 */
    protected final StringBuffer translatePrefixTerm(
	    Term term, String name, int brackets, int skolemization, Vector quantifiedVars) 
	    throws SimplifyException {
	StringBuffer sb = new StringBuffer();
	StringBuffer hb = new StringBuffer();
	switch (brackets) {
	case PREDICATE : sb.append('[');break;
	case BOOLEAN : sb.append('[');break;
	case FUNCTION : sb.append('(');break;
	}
	
	sb.append(name);
	if (term.arity() > 0) {
	    switch (brackets) {
	    case BOOLEAN : sb.append('[');break;
	    case PREDICATE : 
	    case FUNCTION : sb.append('(');break;
	    }
	    for (int i = 0; i < term.arity(); ++i) {
		Debug.assertTrue(term.varsBoundHere(i).size() == 0);
		if (i > 0) {
		    sb.append(", ");
		}
		hb = translate(term.sub(i), skolemization, quantifiedVars);
		if (hb.length() > 0) {
		    sb.append(hb);
		} else {
		    return new StringBuffer();
		}
	    }
	    switch (brackets) {
	    case BOOLEAN : sb.append(']');break;
	    case PREDICATE : 
	    case FUNCTION : sb.append(')');break;
	    }

	} 
	switch (brackets) {
	case PREDICATE : sb.append(DecisionProcedureICSOp.EQUALS).append(TRUEVAL).append(']');break;
	case BOOLEAN : sb.append(']');break;
	case FUNCTION  : sb.append(')');break;
	}
	return sb;
    }

    /**
	 * Takes an AttributeOp like a.b and translates into a_1(b_2)
	 * 
	 * @param term
	 *           The term to be converted.
	 * @param skolemization
	 *           Indicates whether the formula is in the ANTECEDENT, SUCCEDENT
	 *           or with YESNOT if a "not" operation occurres above the term
	 *           which will prevent skolemization ("not"s are not counted).
	 * @param quantifiedVars
	 *           a Vector containing all variables that have been bound in
	 *           super-terms. It is only used for the translation of modulo
	 *           terms, but must be looped through until we get there
	 */
    protected final StringBuffer translateAttributeOpTerm(Term term, int skolemization, Vector quantifiedVars) 
	    throws SimplifyException {
	StringBuffer sb = new StringBuffer();
	StringBuffer hb = new StringBuffer();

	sb.append(getUniqueVariableName(term.op()));
	sb.append('(');
	Debug.assertTrue(term.varsBoundHere(0).size() == 0);
	hb = translate(term.sub(0), skolemization, quantifiedVars);
	if (hb.length() > 0) {
	    sb.append(hb);
	} else {
	    return new StringBuffer();
	}
	sb.append(')');
	return sb;
    }


    /**
	 * Takes a binary infix-term and translates it with its arguments into the
	 * ICS syntax. Examples are x > y, [x | y]
	 * 
	 * @param term
	 *           The term to be converted.
	 * @param name
	 *           The name that should be used for the term (should be unique,
	 *           it should be taken care of that somewhere else (if desired)).
	 * @param brackets
	 *           logical terms can (and should) be put into brackets (if they
	 *           are composite), function terms into rounded parantheses;
	 *           indicate that with one of NONE, BOOLEAN, FUNCTION or PREDICATE
	 * @param skolemization
	 *           Indicates whether the formula is in the ANTECEDENT, SUCCEDENT
	 *           or with YESNOT if a "not" operation occurres above the term
	 *           which will prevent skolemization ("not"s are not counted).
	 * @param quantifiedVars
	 *           a Vector containing all variables that have been bound in
	 *           super-terms. It is only used for the translation of modulo
	 *           terms, but must be looped through until we get there
	 */
    protected final StringBuffer translateBinaryInfixTerm(
	    Term term, String name, int brackets, int skolemization, Vector quantifiedVars) 
	    throws SimplifyException {
	StringBuffer sb = new StringBuffer();
	StringBuffer hb = new StringBuffer();
	Debug.assertTrue(term.varsBoundHere(0).size() == 0);
	Debug.assertTrue(term.varsBoundHere(1).size() == 0);
	Debug.assertTrue(term.arity() == 2);
	switch (brackets) {
	   case BOOLEAN : sb.append('[');break;
	   case FUNCTION : sb.append('(');break;
	}
	hb = translate(term.sub(0), skolemization, quantifiedVars);
	if (hb.length() > 0) {
	    sb.append(hb);
	} else {
	    return new StringBuffer();
	}
	sb.append(name);
	hb = translate(term.sub(1), skolemization, quantifiedVars);
	if (hb.length() > 0) {
	    sb.append(hb);
	} else {
	    return new StringBuffer();
	}
	switch (brackets) {
	   case BOOLEAN : sb.append(']');break;
	   case FUNCTION : sb.append(')');break;
	}
	return sb;
    }


    /**
     * Adds a predicate to the internal set and adds a line to declare the 
     *    predicate to the declarator stringbuffer.
     * This is Simplify stuff. What does it do here? TOD
     * @param name The name of the predicate 
     * (no KeY representation of it has to exist, sometimes constructs not 
     * supported by ICS are mapped to predicates).
     * @param arity The arity of the term.
     */
    protected final void addPredicate(String name, int arity) {
	if (!predicateSet.contains(name)) {
	    predicateSet.add(name);
	    predicate.append("(DEFPRED (").append(name);
	    for (int i = 0; i < arity; ++i) {
		predicate.append(" x").append(i);
	    }
	    predicate.append("))\n");
	}
    }

    /**
     * For some terms (AttributeOps) the order in KeY is different
     * than the order of the user or Simplify expects.
     *
     * @return the simplified version of the Term t in reversed order
     * @param t the Term which should be written in Simplify syntax,
     * but in reverse order compared to the internal order in KeY
     */
    protected final StringBuffer printlastfirst(Term t) {
	StringBuffer sb = new StringBuffer();
	if (t.op().arity() > 0) {
	    Debug.assertTrue(t.op().arity() == 1);
	    sb.append(printlastfirst(t.sub(0)));
	    //sb.append('.');
	}
	sb.append(t.op().name())
	    .append("_")
	    .append(getUniqueHashCode(t.op()));
	return sb;
    }

    protected final StringBuffer signatures = new StringBuffer();
    protected final HashSet sigTable = new HashSet();
    
    protected static final int NONE = 0;
    protected static final int BOOLEAN = 1;
    protected static final int FUNCTION = 2;
    protected static final int PREDICATE = 3;

    protected static String TRUEVAL = "true";

    static Logger logger = Logger.getLogger(ICSTranslation.class.getName());
}
