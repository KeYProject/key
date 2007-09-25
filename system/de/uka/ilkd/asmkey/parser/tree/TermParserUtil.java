// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.tree;


import de.uka.ilkd.asmkey.logic.AsmJunctor;
import de.uka.ilkd.asmkey.logic.AsmOperator;
import de.uka.ilkd.asmkey.logic.TermIfOperator;
import de.uka.ilkd.asmkey.parser.ast.*;
import de.uka.ilkd.asmkey.parser.env.EnvironmentUtil;
import de.uka.ilkd.asmkey.parser.env.TermEnvironment;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator2;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;


/** Helper class to create new terms and convert operators and
 * quantifiers.
 *
 * @author Hubert Schmid
 */

final class TermParserUtil {

    private static final Term[] EMPTY_TERMS = new Term[] {};

    /** Create a nullary term with the given operator. */
    protected static Term createTerm(Operator2 op) throws TermNotValidException
    {
	try {
	    return op.createTerm(null, EMPTY_TERMS);
	} catch (IllegalArgumentException e) {
	    throw new TermNotValidException(e.getMessage());
	} catch (TermCreationException e) {
	    throw new TermNotValidException(e.getMessage());
	}
    }

    /** Create an unary term with the given operator. */
    protected static Term createTerm(Operator2 op, Term term)
	throws TermNotValidException {
	try {
	    return op.createTerm(null, new Term[] { term });
	} catch (IllegalArgumentException e) {
	    throw new TermNotValidException(e.getMessage());
	} catch (TermCreationException e) {
	    throw new TermNotValidException(e.getMessage());
	}
    }

    /** Create a binary term with the given operator. */
    protected static Term createTerm(Operator2 op, Term term1, Term term2) 
	throws TermNotValidException {
	try {
	    return op.createTerm(null, new Term[] { term1, term2 });
	} catch (IllegalArgumentException e) {
	    throw new TermNotValidException(e.getMessage());
	} catch (TermCreationException e) {
	    throw new TermNotValidException(e.getMessage());
	}
    }

    /** Create a ternary term with the given operator. */
    protected static Term createTerm(Operator2 op, Term term1, Term term2, Term term3) 
	throws TermNotValidException {
	try {
	    return op.createTerm(null, new Term[] { term1, term2, term3 });
	} catch (IllegalArgumentException e) {
	    throw new TermNotValidException(e.getMessage());
	} catch (TermCreationException e) {
	    throw new TermNotValidException(e.getMessage());
	}
    }

    /** Create a n-ary term with the given operator */
    protected static Term createTerm(Operator2 op, Term terms[]) 
	throws TermNotValidException {
	try {
	    return op.createTerm(null, terms);
	} catch (IllegalArgumentException e) {
	    throw new TermNotValidException(e.getMessage());
	} catch (TermCreationException e) {
	    throw new TermNotValidException(e.getMessage());
	}
    }

    /** Create a term with a bound variable. */
    protected static Term createTerm(Operator2 op,
                                     QuantifiableVariable v,
                                     Term term1,
                                     Term term2) 
	throws TermNotValidException {

	try {
	    return op.createTerm(new ArrayOfQuantifiableVariable(new QuantifiableVariable[] { v }),
				 new Term[] { term1, term2 });
	} catch (IllegalArgumentException e) {
	    throw new TermNotValidException(e.getMessage());
	} catch (TermCreationException e) {
	    throw new TermNotValidException(e.getMessage());
	}
    }

    /** create a set term */
    //protected static Term createSetTerm(Term[] elems) {
	//Term temp = createTerm(AsmOperator.EMPTY_SET);
	//
	//if (elems != null) {
	//    for (int i = elems.length-1; i>=0; i--) {
	//	temp = createTerm(AsmOperator.SET, elems[i], temp).checked();
	//    }
	//}
	//return temp;
    //}

    /** Create a sequence term */
    protected static Term createSequenceTerm(Sort sort, Term[] elems, Term tail,
					     Operator2 empty, Operator2 cons)
    throws TermNotValidException {
	Term temp = tail==null?(createTerm(empty)):tail;

	if (elems != null) {
	    for (int i=elems.length-1;i >= 0; i--) {
		temp = createTerm(cons, elems[i], temp).checked();
	    }
	}
	return temp;
    }

    /** Converts an AST operator into a logic operator. */
    protected static de.uka.ilkd.key.logic.op.Operator convertOp(TermEnvironment env,
                                                                 AstOperator token)
        throws ParserException
    {
        Operator op = token.getOperator();
        if (op == Operator.IMP) {
            return Op.IMP;
        } else if (op == Operator.OR) {
            return Op.OR;
        } else if (op == Operator.AND) {
            return Op.AND;
        } else if (op == Operator.NOT) {
            return Op.NOT;
        } else if (op == Operator.TRUE) {
            return Op.TRUE;
        } else if (op == Operator.FALSE) {
            return Op.FALSE;
        } else if (op == Operator.ADD) {
            return EnvironmentUtil.getOperator(env, new Identifier(token.getLocation(), "Int.~p"));
        } else if (op == Operator.SUB) {
            return EnvironmentUtil.getOperator(env, new Identifier(token.getLocation(), "Int.~d"));
        } else if (op == Operator.MULT) {
            return EnvironmentUtil.getOperator(env, new Identifier(token.getLocation(), "Int.mul"));
        } else if (op == Operator.DIV) {
            return EnvironmentUtil.getOperator(env, new Identifier(token.getLocation(), "Int.div"));
        } else if (op == Operator.NEG) {
            return EnvironmentUtil.getOperator(env, new Identifier(token.getLocation(), "Int.~m"));
	} else if (op == Operator.STEP) {
	    return AsmJunctor.TIMED;
	} else if (op == Operator.TERM_IF) {
	    return TermIfOperator.OPERATOR;
	} else if (op == Operator.TERM_AND) {
	    return AsmOperator.TERM_AND;
	} else if (op == Operator.TERM_ANDALSO) {
	    return AsmOperator.TERM_ANDALSO;
	} else if (op == Operator.TERM_OR) {
	    return AsmOperator.TERM_OR;
	} else if (op == Operator.TERM_ORELSE) {
	    return AsmOperator.TERM_ORELSE;
	} else if (op == Operator.TERM_EQUALS) {
	    return AsmOperator.TERM_EQUALS;
	} else {
            throw new ParserException("Unknown operator " + op + ".", token.getLocation());
        }
    }

    /** Converts an AST quantifier into a logic quantifier. */
    protected static de.uka.ilkd.key.logic.op.Quantifier convertQuantifier(AstQuantifier token)
        throws ParserException
    {
        Quantifier q = token.getQuantifier();
        if (q == Quantifier.ALL) {
            return Op.ALL;
        } else if (q == Quantifier.EX) {
            return Op.EX;
        } else {
            throw new ParserException("Unknown quantifier " + q + ".",
					      token.getLocation());
        }
    }

    /** Converts an identifier into a name */
    public static Name toName(Identifier id) {
	return new Name(id.getText());
    }
    
    /** Converts an identifier array into a name array */
    public static Name[] toName(Identifier[] id) {
	if (id == null) {
	    return null;
	} else {
	    Name[] names = new Name[id.length];
	    
	    for(int i = 0; i<names.length; i++) {
		names[i] = toName(id[i]);
	    }
	
	    return names;
	}
    }

}
