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

import de.uka.ilkd.asmkey.parser.ast.AstMultiPassDeclaration;
import de.uka.ilkd.asmkey.parser.ast.AstSinglePassDeclaration;
import de.uka.ilkd.asmkey.parser.ast.AstUnitDeclarations;
import de.uka.ilkd.asmkey.parser.env.DeclarationEnvironment;
import de.uka.ilkd.asmkey.unit.UnitParser;
import de.uka.ilkd.key.parser.ParserException;

/**
 * we use a factory to allow the 
 * test of the different passes of the parser
 * @see DeclarationParser
 * @see UnitParser
 * @see TestFirstPass
 */
public abstract class DeclarationParserFactory {


    public abstract DeclarationParser getParser(DeclarationEnvironment env);

    
    /* --- default with all passes --- */
    public static DeclarationParserFactory DEFAULT = 
	new DeclarationParserFactory() {
	    public DeclarationParser getParser(DeclarationEnvironment env) {
		return new DeclarationParser(env) {
			
			public void parse(AstUnitDeclarations decls) throws ParserException {
			    AstSinglePassDeclaration[] early =
				decls.getEarlySinglePassDeclarations();
			    AstMultiPassDeclaration[] multi = 
				decls.getMultiPassDeclarations();
			    AstSinglePassDeclaration[] late = 
				decls.getLateSinglePassDeclarations();
			    for (int i = 0; i < early.length; ++i) {
				parseSingle(early[i]);
			    }
			    for (int i = 0; i < multi.length; i++) {
				parseFirstPass(multi[i]);
			    }
			    for (int i = 0; i < multi.length; i++) {
				parseSecondPass(multi[i]);
			    }
			    DerivedFunctionParser parser = 
				new DerivedFunctionParser(this.env, this.deriveds);
			    parser.doAnalysis();
			    parser.replaceSymbols();
			    for (int i = 0; i < late.length; i++) {
				parseSingle(late[i]);
			    }
			}
			
		    };
	    }
	};

}
