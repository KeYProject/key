// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.env;


import de.uka.ilkd.asmkey.logic.AsmRule;
import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.asmkey.parser.ast.AstType;
import de.uka.ilkd.asmkey.parser.ast.Identifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.rule.RuleSet;


/** Utility class that capsulates all method calls to TermEnvironment
 * and DeclarationEnvironment. If the forwarded method calls throws an
 * EnvironmentException, the exception is catched and an approtiate
 * ParserException is thrown instead.
 *
 * @author Hubert Schmid
 */

public final class EnvironmentUtil {

    public static SchemaVariable getSchemaVariable(TermEnvironment env, Identifier id)
	throws ParserException {
        try {
            return env.getSchemaVariable(id.name());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    public static Sort getSort(SortEnvironment env, AstType type) throws ParserException {
        try {
	    Sort sort = env.getSort(type.getSort().name());
	    if (type.isList()) {
		if(sort instanceof PrimitiveSort) {
		    sort = ((PrimitiveSort)sort).getSequenceSort();
		} else {
		    throw new EnvironmentException("The sort " + sort.name() +
						   "is not NonCollection and may not" +
						   "be elements of a list.");
		}
	    }
            return sort;
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), type.getLocation());
        }
    }

    public static Sort getSort(SortEnvironment env, Identifier id) throws ParserException {
        try {
            return env.getSort(id.name());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    public static de.uka.ilkd.key.logic.op.Operator getOperator(TermEnvironment env, Identifier id)
        throws ParserException {
        try {
            return env.getOperator(id.name());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    public static MetaOperator getMetaOp(TermEnvironment env, Identifier id) throws ParserException {
        try {
            return env.getMetaOp(id.name());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    public static AsmRule getRule(TermEnvironment env, Identifier id) throws ParserException {
        try {
            return env.getRule(id.name());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    public static Term getAbbreviatedTerm(TermEnvironment env, Identifier id) throws ParserException {
        try {
            return env.getAbbreviatedTerm(id.getText());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

    public static RuleSet getRuleSet(DeclarationEnvironment env, Identifier id)
	throws ParserException {
        try {
            return env.getRuleSet(id.name());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(), id.getLocation());
        }
    }

}
