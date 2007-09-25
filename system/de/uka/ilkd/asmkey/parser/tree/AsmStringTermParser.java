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


import java.io.Reader;

import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.asmkey.parser.AstParser;
import de.uka.ilkd.asmkey.parser.ast.AstAsmRule;
import de.uka.ilkd.asmkey.parser.ast.AstTerm;
import de.uka.ilkd.asmkey.parser.env.DefaultEnvironment;
import de.uka.ilkd.asmkey.parser.env.ProcedurePool;
import de.uka.ilkd.asmkey.parser.env.TermEnvironment;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.ListOfOperator;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SLListOfOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.SimpleTermParser;
import de.uka.ilkd.key.pp.AbbrevMap;


/** This class implements the {@link
 * de.uka.ilkd.key.parser.SimpleTermParser} interface to parse asm
 * terms and rules.
 *
 * @author Hubert Schmid */

public final class AsmStringTermParser implements SimpleTermParser {

    /** Create and return a collection, that contains all elements
     * from the given namespace. */
    /*private static Collection toCollection(Namespace ns) {
        List list = new ArrayList();
        for (IteratorOfNamed i = ns.allElements().iterator(); i.hasNext();) {
            list.add(i.next());
        }
        return list;
	}*/

    /** Create and return a collection, that contains all logic
     * variables from the given namespace. */
    private static ListOfOperator getLogicVariables(Namespace ns) {
        ListOfOperator list = SLListOfOperator.EMPTY_LIST;
        for (IteratorOfNamed i = ns.allElements().iterator(); i.hasNext();) {
            Named v = i.next();
            if (v instanceof LogicVariable) {
                list = list.prepend((LogicVariable) v);
            }
        }
        return list;
    }


    public Term parse(Reader in,
		      Sort sort,
		      Services services,
		      NamespaceSet ns,
		      AbbrevMap abbreviations) 
	throws ParserException{
	return parse(in, sort, services,
		     ns.variables(), ns.functions(), ns.sorts(), ns.programVariables(),
		     abbreviations);
    }

    public Term parse(Reader in,
                      Sort sort,
                      Services services,
                      Namespace varNS,
                      Namespace func_ns,
                      Namespace sort_ns,
		      Namespace progVar_ns,
                      AbbrevMap abbreviations)
        throws ParserException {
        Term term;
        TermEnvironment env =
            new DefaultEnvironment(null,
                                   sort_ns,
                                   null,
                                   func_ns,
                                   ProcedurePool.get(services),
                                   null,
                                   null,
				   null,
				   null,
				   null,
                                   new AbbreviationWrapper(abbreviations)); // or null ????
	return parse(in, sort, varNS, env);
    }


    private Term parse(Reader in, Sort sort, Namespace varNS, TermEnvironment env) 
	throws ParserException {
	Term term;

	if (sort == PrimitiveSort.ASMRULE) {
            AstAsmRule asmRule = AstParser.parseAsmRule(in);
            term = TermParser.parseAsmRule(env, asmRule, getLogicVariables(varNS));
        } else {
            AstTerm astTerm = AstParser.parseTerm(in);
            term = TermParser.parseTerm(env, astTerm, getLogicVariables(varNS));
        }
	/* not necessary, we have no object types susceptible of transitivity
	 * TO CHECK
        if (sort != null && !term.sort().extendsTrans(sort)) {
            throw new ParserException("parsed " + term.sort() + " where " + sort + " was expected.",
                                      null);
				      }*/
        return term;
    }

}
