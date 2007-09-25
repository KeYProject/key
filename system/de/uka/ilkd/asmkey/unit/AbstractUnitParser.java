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

import de.uka.ilkd.asmkey.parser.ast.*;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParser;
import de.uka.ilkd.asmkey.parser.tree.DeclarationParserFactory;
import de.uka.ilkd.asmkey.storage.StorageException;
import de.uka.ilkd.asmkey.storage.StorageManager;
import de.uka.ilkd.asmkey.unit.base.BaseUnit;
import de.uka.ilkd.asmkey.unit.base.BaseUnitParser;
import de.uka.ilkd.asmkey.util.graph.CycleException;
import de.uka.ilkd.asmkey.util.graph.GraphException;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;


/** the abstract unit parser class is the ancestor 
 * of the class responsible for loading the units, under the
 * supervison of the {@link UnitManager}. The class
 * is abstract and contain all common operation. The class
 * {@link UnitParser} will allow to load user defined units
 * and the class {@link BaseUnitParser} will allow to load
 * the base units (standart library).
 */
public abstract class AbstractUnitParser implements AstImportVisitor { 
  
    protected UnitManager manager;
    protected UnitListener listener;
    protected UnitGraph graph;
    protected StorageManager storage;
    protected DeclarationParserFactory factory;
    protected String project;

    public AbstractUnitParser(UnitManager manager,
			      UnitListener listener,
			      UnitGraph graph,
			      StorageManager storage,
			      DeclarationParserFactory factory,
			      String project) {
	this.manager = manager;
	this.listener = listener;
	this.graph = graph;
	this.storage = storage;
	this.factory = factory;
	this.project = project;
    }

    public AbstractUnitParser(UnitManager manager,
			      UnitListener listener,
			      UnitGraph graph,
			      StorageManager storage,
			      String project) {
	this(manager, listener, graph, storage, DeclarationParserFactory.DEFAULT, project);
    }
     
    /** A derived class must implement this method to get access
     * to its AstUnits. typically it will use its {@link StorageManager}.
     */
    public abstract AstUnit[] getAstUnits()
	throws ParserException, StorageException;

    /**
     * A derived class must implement this method to create new units
     * based on a AstUnit. In particular, it allows {@link BaseUnitParser}
     * to create and load the special {@link BaseUnit} of the standart
     * library.
     */
    public abstract Unit createUnit(AstUnit astunit) throws UnitException;

    /**
     * to do some processing after the parsing has taken place.
     */
    public abstract void postParsing() throws UnitException;

    public void parseUnits() throws ParserException, UnitException {
	AstUnit[] astUnits;
	Unit unit;
	HashMapFromNameToAstUnit astUnitMap;
	
	/* first we set the status */
	listener.loadingInitialLogEntry("=== loading starts", 4);

	/* then we load the units ast trees */
	astUnits = loadAstTrees();
	listener.loadingMinorLogEntry("creating astUnitMap.");
	astUnitMap = UnitUtil.createAstUnitMap(astUnits);
	
	/* then we can populate the graph */
	populateUnitGraph(astUnits);
	parse(astUnits.length);	
	postParsing();
    }

    /** This method loads the ast trees for the units given
     * by the storage manager.
     */
    AstUnit[] loadAstTrees() throws ParserException {
	AstUnit[] astUnits;

	listener.loadingMajorLogEntry("loading the ast trees of the units.", 2);
	try {
	    astUnits = getAstUnits();
	    listener.loadingMinorLogEntry("we have " + astUnits.length + " units.");
	} catch (StorageException e) {
	    throw new ParserException (e.toString(), null);
	}

	return astUnits;
    }

    /** 
     * given an array of astUnits, it creates
     * the units for the unitGraph and 
     * populates it with edges with the information
     * of the AstImportInfo contained in the AstUnit[].
     */
    void populateUnitGraph(AstUnit[] astUnits) throws ParserException, UnitException {
	Unit unit;

	/* We then creates the necessary units and add them to the graph */
	listener.loadingMajorLogEntry("creating the units and adding them to the graph.",
				      astUnits.length);
	for(int i=0; i<astUnits.length; i++) {
	    try {
		unit = createUnit(astUnits[i]);
		this.graph.add(unit);
		listener.loadingMinorLogEntry("done for unit " + unit.name() + ".");
	    } catch (GraphException e) {
		throw new UnitException(e);
	    }
	}
	/* we then add the edges for each import clause in each unit */
	listener.loadingMajorLogEntry("creating dependancy edges.",
				      2*astUnits.length + 2*baseEntries());
	IteratorOfUnit it = graph.iterator();
	AstImport[] imports;
	while(it.hasNext()) {
	    try {
		unit = it.next();
		listener.loadingMinorLogEntry("start for unit=" + unit.name() + ".");
		if (unit.status() == Unit.LOADED) {
		    listener.loadingMinorLogEntry("unit " + unit.name() + " already loaded.");
		} else {
		    imports = unit.astUnit().getImports();
		    for(int j=0; j<imports.length; j++) {
			Name name = imports[j].acceptFirstPass(this);
			Unit unit2 = graph.get(name);
			if (!graph.containsEdge(unit, unit2)) {
			    graph.addEdge(unit, unit2);
			}
		    }
		    /* if the base is loaded, than all added units implicitely use the base. */
		    if (manager.status() == UnitManager.BASE_LOADED) {
			Unit[] base = manager.base();
			for (int j=0; j<base.length; j++) {
			    if (!graph.containsEdge(unit, base[j])) {
				graph.addEdge(unit, base[j]);
			    }
			}
		    }
		    listener.loadingMinorLogEntry("done for unit " + unit.name() + ".");
		}
	    } catch (CycleException e) {
		throw new UnitException(e);
	    }
	}
	
    }
    
    /** first pass of the parsing
     * @see #loadUnits */
    void parse(int loglength) throws ParserException, UnitException {
	/* now the graph is completed, we must load the namespaces
	 * we must first make a topological sort to load the units
	 * in the good order and create the necessary import infos.
	 */
	IteratorOfUnit iterator = graph.orderedIterator();
	AstUnit astUnit;
	DeclarationParser parser;
	Unit unit;

	listener.loadingMajorLogEntry("loading namespaces for units.",
				      2*loglength + 2*baseEntries());
	while(iterator.hasNext()) {
	    unit = iterator.next();
	    listener.loadingMinorLogEntry("beginning for unit=" + unit.name());
	    if (unit.status() == Unit.LOADED) {
		listener.loadingMinorLogEntry("unit " + unit.name() + " already loaded.");
	    } else if (unit.status() == Unit.ERROR) {
		throw new UnitException("A unit with ERROR status has been encountered. " +
					"AsmKeY should have failed before.");
	    } else {
		astUnit = unit.astUnit();
		int base;
		int length;
		/* before we can go to the declarations;
		 * we must first finish the parsing of the AstImport;
		 * and integerate it in the unit to allow proper
		 * loading.
		 */
		AstImport[] imports = astUnit.getImports();
		ImportInfo[] infos;
		/* if the manager has loaded the base units, 
		 * we must import them */
		if (manager.status() == UnitManager.BASE_LOADED) {
		    ImportInfo[] baseInfos = manager.baseImportInfos();
		    boolean[] toInclude = new boolean[baseInfos.length];
		    int included = baseInfos.length;
		    for(int i=0; i<toInclude.length; i++) {
			toInclude[i] = true;
			for(int j=0; j<imports.length; j++) {
			    if (baseInfos[i].unit().name().equals(imports[j].name())) {
				toInclude[i] = false;
				included--;
				break;
			    }
			}
		    }
		    length = imports.length + included;
		    infos = new ImportInfo[length];
		    base = 0;
		    for(int i=0; i<baseInfos.length; i++) {
			if (toInclude[i]) {
			    infos[base] = baseInfos[i];
			    base++;
			}
		    }
		} else {
		    length = imports.length;
		    infos = new ImportInfo[length];
		    base = 0;
		}
		for(int i=base; i<length; i++) {
		    infos[i] = imports[i-base].acceptSecondPass(this);
		}
		unit.setImportInfos(infos);
		/* now, we have secure all in the information to access
		 * the symbols of the imported units; we can
		 * parse the declarations of the current unit.
		 */
		parser = factory.getParser(unit);
		parser.parse(astUnit.getDeclarations());
		/* the unit is loaded */
		unit.setStatus(Unit.LOADED);
		listener.loadingMinorLogEntry("done for unit " + unit.name() + ".");
	    }
	    
	}
    }

    private int baseEntries() throws UnitException {
	if (manager.status() == UnitManager.BASE_LOADED) {
	    return manager.base().length;
	} else {
	    return 0;
	}
    }
    
    /* --- AstImportVisitor implementation --- */

    
    public ImportInfo visitNoSymbolsImport(Identifier unitId, Location location) 
    throws ParserException 
    {
	/* the second visit for a NoSymbolImport is very easy, as
	 * we have already verified in the first pass that the name
	 * really belongs to a unit. we must just check the imported unit
	 * has been correctly loaded.
	 */
	Unit unit = graph.get(new Name(unitId.getText()));
	checkLoadedUnitOrThrowException(unit, "visitNoSymbolImport", unitId.getLocation());
	return ImportInfo.createNoSymbolsImportInfo(unit);
    }

    public ImportInfo visitAllSymbolsImport(Identifier unitId, Location location)
    throws ParserException
    {
	/* same remark as for NoSymbolImport */
	Unit unit = graph.get(new Name(unitId.getText()));
	checkLoadedUnitOrThrowException(unit, "visitAllSymbolsImport", unitId.getLocation());
	return ImportInfo.createAllSymbolsImportInfo(unit);
    }

    public ImportInfo visitSomeSymbolsImport(Identifier unitId, AstRestrictedSymbol[] symbols,
					     Location location) 
	throws ParserException
    {
	/* the second visit of SomeSymbolImport is a bit more complicated 
	 * we must first verify that the imported unit has been
	 * parsed; than that all explicitely imported symbols do exists and
	 * are not local (TODO); if all of this is ok. then
	 * we can create the ImportInfo.
	 */
	Unit unit = graph.get(new Name(unitId.getText()));
	checkLoadedUnitOrThrowException(unit, "visitSomeSymbolsImport", unitId.getLocation());

	RestrictedSymbol symbs[] = new RestrictedSymbol[symbols.length];
	for(int i=0; i<symbols.length; i++) {
	    try {
		symbs[i] = new RestrictedSymbol(symbols[i].type(), symbols[i].symbol().getText());
		if(!unit.containsRestrictedSymbol(symbs[i])) {
		    throw new ParserException("The symbol " + symbs[i].symbol() + " of kind " +
					      RestrictedSymbol.getStringForType(symbs[i].type()) +
					      " is not defined in the unit "
					      + unit + ".", symbols[i].getLocation());
		}
	    } catch (UnitException e) {
		throw new ParserException(e.toString(), symbols[i].getLocation());
	    }
	}
	return ImportInfo.createSomeSymbolsImportInfo(unit, symbs);
    }

    private void checkLoadedUnitOrThrowException(Unit unit, String kind, Location location)
	throws ParserException {
	if(unit.status() != Unit.LOADED) {
	    throw new ParserException(kind + ": the imported unit " + unit.name() +
				      " has not been imported.", location);
	}
    }

    public Name visitImportFirstPass(Identifier unit, Location location) throws ParserException {
	Name name = new Name(unit.getText());
	if (!graph.contains(name)) {
	    throw new ParserException("UnitManager:visitImportFirstPass failed: the unit " +
				      name + " does not exist.", location);
	}
	return name;
    }
}
