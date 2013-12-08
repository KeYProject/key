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


package de.uka.ilkd.key.parser;


import java.io.IOException;
import java.io.Reader;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;


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
                      Namespace var_ns,
                      Namespace func_ns, 
                      Namespace sort_ns,
                      Namespace progVar_ns, 
                      AbbrevMap scm)
        throws ParserException
    {
	return parse(in , sort, services,
		     new NamespaceSet(var_ns,
				      func_ns, 
				      sort_ns, 
				      new Namespace(),
				      new Namespace(),
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
        try{
            KeYParserF parser
                = new KeYParserF(ParserMode.TERM, new KeYLexerF(
		                in,
		                services.getExceptionHandler()), 
		                "",
				new Recoder2KeY (services, nss),
                                services, 
                                nss, 
                                scm);

	    final Term result = parser.term();
	    if (sort != null &&  ! result.sort().extendsTrans(sort))
	        throw new ParserException("Expected sort "+sort+", but parser returns sort "+result.sort()+".", null);
        return result;
        } catch (RecognitionException re) {
            throw new ParserException(re.getMessage(),
                                      new Location(re.getFilename(),
                                                   re.getLine(),
                                                   re.getColumn()));
        } catch (IOException tse) {
            throw new ParserException(tse.getMessage(), null);
        }
    }
    
}
