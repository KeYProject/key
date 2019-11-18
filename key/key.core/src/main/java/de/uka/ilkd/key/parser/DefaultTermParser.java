// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;


import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.rule.RuleSet;
import org.antlr.runtime.RecognitionException;

import java.io.IOException;
import java.io.Reader;


/** This class wraps the default KeY-Term-Parser.
 *
 * @author Hubert Schmid
 */

public final class DefaultTermParser {

    /** The method reads the input and parses a term with the
     * specified namespaces. The method ensures, that the term has the
     * specified sort.
     * @param sort The expected sort of the term.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly or the term has an
     * invalid sort. */    
    public Term parse(Reader in, 
	    	      Sort sort, 
	    	      Services services,
                      Namespace<QuantifiableVariable> var_ns,
                      Namespace<Function> func_ns,
                      Namespace<Sort> sort_ns,
                      Namespace<IProgramVariable> progVar_ns,
                      AbbrevMap scm)
        throws ParserException
    {
	return parse(in , sort, services,
		     new NamespaceSet(var_ns,
				      func_ns, 
				      sort_ns, 
				      new Namespace<RuleSet>(),
				      new Namespace<Choice>(),
				      progVar_ns),		     
		     scm);
    }


    /** The method reads the input and parses a term with the
     * specified namespaces. The method ensures, that the term has the
     * specified sort.
     * @param sort The expected sort of the term; must not be null.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly or the term has an
     * invalid sort. */    
    public Term parse(Reader in, 
	    	      Sort sort, 
	    	      Services services,
                      NamespaceSet nss, 
                      AbbrevMap scm)
        throws ParserException
    {
        KeYParserF parser = null;
        try{
            parser
                = new KeYParserF(ParserMode.TERM, new KeYLexerF(in, ""),
				new Recoder2KeY (services, nss),
                                services, 
                                nss, 
                                scm);

            final Term result = parser.termEOF();
            if (sort != null &&  ! result.sort().extendsTrans(sort))
	        throw new ParserException("Expected sort "+sort+", but parser returns sort "+result.sort()+".", null);
        return result;
        } catch (RecognitionException re) {
            // problemParser cannot be null since exception is thrown during parsing.
            String message = parser.getErrorMessage(re);
            throw new ParserException(message, new Location(re)).initCause(re);
        } catch (IOException tse) {
            throw new ParserException(tse.getMessage(), null).initCause(tse);
        }
    }
    
     /**
     * The method reads the input and parses a sequent with the
     * specified namespaces.
     * @return the paresed String as Sequent Object
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly
     */
    public Sequent parseSeq(Reader in, Services services, NamespaceSet nss, AbbrevMap scm) 
            throws ParserException {
        KeYParserF p = null;
        try {
            p = new KeYParserF(ParserMode.TERM, new KeYLexerF(in, ""), new Recoder2KeY(services, nss), services, nss, scm);
            final Sequent seq = p.seqEOF();
                return seq;
        } catch (RecognitionException re) {
            // problemParser cannot be null since exception is thrown during parsing.
            String message = p.getErrorMessage(re);
            throw new ParserException(message, new Location(re));
        } catch (IOException tse) {
            throw new ParserException(tse.getMessage(), null);
        }
    }

    
}
