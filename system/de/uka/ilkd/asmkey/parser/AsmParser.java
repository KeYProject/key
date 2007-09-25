// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.parser;

import java.io.Reader;

import de.uka.ilkd.asmkey.proof.init.InitConfig;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.proof.init.ModStrategy;


/** Static methods to parse files and part of files
 * (sorts, functions, etc....)
 *
 * @author Hubert Schmid
 */

public class AsmParser {

    public static void parseDeclarations(Reader reader, InitConfig init, ModStrategy mod)
	throws ParserException
    {
	//TreeParser.parseDeclarations(init.env(), AstParser.parseDeclarations(reader), mod);
    }

    //public static void parseImportDeclarations(Reader reader, InitConfig init, ModStrategy mod);

    // public static void parseImportLemmas(Reader reader, InitConfig init, ModStrategy mod);



}
