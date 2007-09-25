// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

import de.uka.ilkd.asmkey.parser.ast.AstUnit;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.asmkey.storage.StorageException;
import de.uka.ilkd.asmkey.storage.StorageManager;
import de.uka.ilkd.key.parser.ParserException;


/** This class is responsible for loading the user defined units.
 * for the sake of the simplicity, we always load ALL user defined
 * units.
 */
public class UnitParser extends AbstractUnitParser { 
  
    UnitParser(UnitManager manager,
	       UnitListener listener,
	       UnitGraph graph,
	       StorageManager storage,
	       DeclarationParserFactory factory,
	       String project) {
	super(manager, listener, graph, storage, factory, project);
    }

    public UnitParser(UnitManager manager,
		      UnitListener listener, UnitGraph graph, StorageManager storage,
		      String project) {
	super(manager, listener, graph, storage, project);
    }

    public AstUnit[] getAstUnits() throws ParserException, StorageException {
	return storage.getUnitAstTrees(project);
    }

    public Unit createUnit(AstUnit astunit) {
	return new Unit(astunit); 
    }

    public void postParsing() {
	
    }

}
