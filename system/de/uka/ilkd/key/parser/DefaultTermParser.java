// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;


import java.io.Reader;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;


/** Defaut implementation of SimpleTermParser. This class wraps the
 * default KeY-Term-Parser in the SimpleTermParser interface.
 *
 * @author Hubert Schmid
 */

public final class DefaultTermParser implements SimpleTermParser {

    /* --- methods --- */

    public Term parse(Reader in, Sort sort, Services services,
                      Namespace var_ns, Namespace func_ns, Namespace sort_ns,
                      Namespace progVar_ns, AbbrevMap scm)
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


    public Term parse(Reader in, Sort sort, Services services,
                      NamespaceSet nss, AbbrevMap scm)
        throws ParserException
    {
        try{
            KeYParser parser
                = new KeYParser(ParserMode.TERM, new KeYLexer(
		                in,services.getExceptionHandler()), "",
				TermFactory.DEFAULT,
				new Recoder2KeY (services, nss),
                                services, nss, scm);

	    return parser.term();
        } catch (RecognitionException re) {
            throw new ParserException(re.getMessage(),
                                      new Location(re.getFilename(),
                                                   re.getLine(),
                                                   re.getColumn()));
        } catch (TokenStreamException tse) {
            throw new ParserException(tse.getMessage(), null);
        }
    }

}
