// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//

package de.uka.ilkd.key.parser;

import java.io.Reader;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.AbbrevMap;

/** A simple interface to parse arbitrary terms.
 *
 * @author Hubert Schmid
 */

public interface SimpleTermParser {

    /** The method reads the input and parses a term with the
     * specified namespaces. The method ensures, that the term has the
     * specified sort.
     * @param sort The expected sort of the term.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly or the term has an
     * invalid sort. */
    Term parse(Reader in, Sort sort, Services services,
               Namespace varNS, Namespace func_ns, Namespace sort_ns,
               Namespace progVar_ns, AbbrevMap scm)
        throws ParserException;

    /** The method reads the input and parses a term with the
     * specified namespaces. The method ensures, that the term has the
     * specified sort.
     * @param sort The expected sort of the term.
     * @return The parsed term of the specified sort.
     * @throws ParserException The method throws a ParserException, if
     * the input could not be parsed correctly or the term has an
     * invalid sort. */
    Term parse(Reader in, Sort sort, Services services,
               NamespaceSet nss, AbbrevMap scm)
        throws ParserException;

}
