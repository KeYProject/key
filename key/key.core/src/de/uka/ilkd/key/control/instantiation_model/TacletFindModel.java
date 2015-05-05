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

package de.uka.ilkd.key.control.instantiation_model;

import java.io.StringReader;
import java.util.ArrayList;
import java.util.Iterator;

import javax.swing.table.AbstractTableModel;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableMapEntry;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.IdDeclaration;
import de.uka.ilkd.key.parser.KeYLexerF;
import de.uka.ilkd.key.parser.KeYParserF;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.InstantiationProposerCollection;
import de.uka.ilkd.key.proof.MissingInstantiationException;
import de.uka.ilkd.key.proof.MissingSortException;
import de.uka.ilkd.key.proof.SVInstantiationException;
import de.uka.ilkd.key.proof.SVInstantiationParserException;
import de.uka.ilkd.key.proof.SVRigidnessException;
import de.uka.ilkd.key.proof.SortMismatchException;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.RigidnessException;
import de.uka.ilkd.key.rule.inst.SortException;
import de.uka.ilkd.key.util.Pair;


public class TacletFindModel extends AbstractTableModel {

    /**
     * 
     */
    private static final long serialVersionUID = 5285420522875326156L;
    /** the instantiations entries */
    private ArrayList<Pair<SchemaVariable, String>> entries;
    /** the related rule application */
    private final TacletApp originalApp;
    /** the integer defines the row until which no editing is possible */
    private int noEditRow;
    /** universal namespace of variables, minimum for input in a row */
    private NamespaceSet nss;
    /** the java service object */
    private Services services;
    /** the abbreviation map */
    private AbbrevMap scm;
    /** the current goal */
    private Goal goal;
    /** variable namer */
    private VariableNamer varNamer;
    /** proposers to ask when instantiating a schema variable */
    private InstantiationProposerCollection instantiationProposers;


    /** create new data model for tree
     * @param app the TacletApp where to get the necessary entries
     */
    public TacletFindModel(TacletApp    app, 
					  Services     services,
					  NamespaceSet nss,
					  AbbrevMap    scm,
					  Goal	       goal) {
	this.originalApp = app;
       
	this.nss = nss;
	this.services = services;
	this.scm = scm;
	this.goal = goal;
	this.varNamer = services.getVariableNamer();
	
	instantiationProposers = new InstantiationProposerCollection();
	instantiationProposers.add(varNamer);
	instantiationProposers.add(VariableNameProposer.DEFAULT);
	
	entries = createEntryArray(app);
    }

    /**
     * returns the set of namespaces
     */
    private NamespaceSet namespaces() {
        return nss;
    }

    /** creates a Vector with the row entries of the table
    */
    private ArrayList<Pair<SchemaVariable, String>> createEntryArray(TacletApp tacletApp) {
        ArrayList<Pair<SchemaVariable, String>> rowVec = new ArrayList<>();
        final Iterator<ImmutableMapEntry<SchemaVariable, InstantiationEntry<?>>> it = tacletApp.instantiations().pairIterator();
        int count = 0;

        while (it.hasNext()) {
            final ImmutableMapEntry<SchemaVariable,InstantiationEntry<?>> entry = it.next();            
            rowVec.add(new Pair<SchemaVariable, String>(entry.key(), ProofSaver.printAnything(entry.value(), services)));
            count++;
        }

        noEditRow = count - 1;

        ImmutableList<String> proposals = ImmutableSLList.<String>nil();

        for (SchemaVariable var: tacletApp.uninstantiatedVars()) {

            if (!tacletApp.taclet ().getIfFindVariables ().contains(var)) {
                // create an appropriate and unique proposal for the name ...
                String proposal
                        = instantiationProposers.getProposal(tacletApp,
                                                             var,
                                                             services,
                                                             goal.node(),
                                                             proposals);


                Pair<SchemaVariable, String> pair = new Pair<>(var, proposal);

                if(proposal != null) {
                    // A proposal is available ...
                    proposals = proposals.append(proposal);
                }
                
                rowVec.add(pair);
            }
        }

        return rowVec;
    }


    /** 
     * number of columns
     * @return number of columns
     */
    @Override
    public int getColumnCount() {
        return 2;
    }

    /** number of rows
     * @return number of rows
     */
    @Override
    public int getRowCount() {
        return entries.size();
    }

    /** returns true iff an instantiation is missing
     * @return true iff an instantiation is missing
     */
    @Override
    public boolean isCellEditable(int rowIndex, int columnIndex) {
        return (rowIndex > noEditRow) && (columnIndex > 0);
    }


    /** parses the given string that represents the term (or formula)
     * using the given variable namespace and the given namespace
     * for functions and default namespaces for the others
     * @param s the String to parse
     * @param varNS the variable namespace
     * @param functNS the function namespace
     */
    private Term parseTerm(String s, Namespace varNS, Namespace functNS)
        throws ParserException
    {
        NamespaceSet copy = nss.copy();
        copy.setVariables(varNS);
        copy.setFunctions(functNS);
        Term term = new DefaultTermParser().parse(
           new StringReader(s), null, services, copy, scm);
        return term;
    }

    /**
     * Parse the declaration of an identifier (i.e. the declaration of
     * a variable or skolem function)
     */
    private IdDeclaration parseIdDeclaration ( String s )
        throws ParserException {
        KeYParserF parser = null;
        try {
            parser =
                new KeYParserF (ParserMode.DECLARATION, new KeYLexerF ( s, ""),
                                 services,   // should not be needed
                                 nss );
            return parser.id_declaration ();
        } catch (RecognitionException re) {
            // parser cannot be null
            throw new ParserException(parser.getErrorMessage(re), new Location(re));
        }
    }

    /**
     * throws an exception iff no input in indicated row, and no
     * metavariable instantiation is possible
     *
     */

    private void checkNeededInputAvailable(int irow)
        throws MissingInstantiationException {

        final int icol = 1;

        if ( ( getValueAt(irow, icol) == null  ||
               ((String)getValueAt(irow, icol)).length() == 0 ) &&
               !originalApp.complete() ) {
            throw new MissingInstantiationException
                ("" + getValueAt(irow, 0), irow, 0, false);
        }
    }



    /**
     * @return true iff this row is not empty (i.e. a string of data
     * is available)
     */
    private boolean isInputAvailable(int irow) {
        return getValueAt(irow, 1) != null && ((String)getValueAt(irow,1)).length() != 0;
    }

    /**
     * parses the indicated row and returns a Term corresponding to the
     * entry in the row
     *
     * @param irow the row to be parsed
     * @param varNS the variable namespace that will be passed to parseTerm
     * @param functNS the function namespace that will be passed to parseTerm
     * @return the parsed term
     */
    private Term parseRow(int irow, Namespace varNS, Namespace functNS)
        throws SVInstantiationParserException,
               MissingInstantiationException {

        String instantiation = (String) getValueAt(irow, 1);

        if ( instantiation == null || "".equals(instantiation) ) {
            throw new MissingInstantiationException("", irow, 0, false);
        }

        try {
            return parseTerm(instantiation, varNS, functNS);
        } catch (ParserException pe) {
            Location loc = pe.getLocation();
            if (loc != null) {
                throw new SVInstantiationParserException(instantiation,
                                                         irow + (loc.getLine() <= 0 ? 0
                                                                 : loc.getLine()),
                                                         loc.getColumn(), pe.getMessage(),
                                                         false);
            } else {
                throw new SVInstantiationParserException(instantiation,
                                                         irow, -1,
                                                         pe.getMessage(),
                                                         false);
            }
        }
    }

    /**
     * parses the indicated row and returns a identifier declaration
     * corresponding to the entry in the row
     *
     * @param irow the row to be parsed
     * @return the parsed declaration
     */
    private IdDeclaration parseIdDeclaration(int irow)
        throws SVInstantiationParserException,
               MissingInstantiationException {

        String instantiation = (String) getValueAt(irow, 1);

        if ( instantiation == null || "".equals(instantiation) ) {
            throw new MissingInstantiationException("", irow, 0, false);
        }

        try {
            return parseIdDeclaration(instantiation);
        } catch (ParserException pe) {
            Location loc = pe.getLocation();
            if (loc != null) {
                throw new SVInstantiationParserException(instantiation,
                                                         irow + (loc.getLine() <= 0 ? 0
                                                                 : loc.getLine()),
                                                         loc.getColumn(), pe.getMessage(),
                                                         false);
            } else {
                throw new SVInstantiationParserException(instantiation,
                                                         irow, -1,
                                                         pe.getMessage(),
                                                         false);
            }
        }
    }

    /**
     * parses the indicated row and returns the ProgramElement
     * corresponding to the entry in the row
     * @param irow the row to be parsed
     * @return the parsed term
     */
    private ProgramElement parseRow(int irow)
        throws SVInstantiationParserException {

        String instantiation = (String) getValueAt(irow, 1);
        SchemaVariable sv = (SchemaVariable)getValueAt(irow, 0);

        ContextInstantiationEntry contextInstantiation = 
            originalApp.instantiations().getContextInstantiation();
        
        final PosInProgram prefix;
        if (contextInstantiation == null) {
            prefix = PosInProgram.TOP;
        } else {
            prefix = contextInstantiation.prefix();
        }
        
	if(! varNamer.isUniqueNameForSchemaVariable(
			instantiation,
    			sv,
			originalApp.posInOccurrence(),
			prefix)) {
	    throw new SVInstantiationParserException(instantiation,
	    					     irow,
						     0,
						     "Name is already in use.",
						     false);
	}


	ProgramElement pe = originalApp.getProgramElement(instantiation, sv, services);
	if (pe == null) {
	    throw new SVInstantiationParserException
		(instantiation, irow, -1, "Unexpected sort: "
		 + sv.sort()
		 + "." + "Label SV or a program variable SV expected"
		 + " declared as new.", false);
	}
	return pe;
    }
    
    
    /**
     * creates new rule app with all inserted instantiations in the variable
     * instantiations table
     * @throws SVInstantiationException if the instantiation is incorrect
     */
    public TacletApp createTacletAppFromVarInsts()
        throws SVInstantiationException {

        final TermBuilder tb = services.getTermBuilder();
	TacletApp      result = originalApp;
	SchemaVariable sv     = null;
	Sort           sort   = null;
	int            irow   = 0;

        try {

	    for (irow = noEditRow+1; irow < entries.size(); irow++) {
                checkNeededInputAvailable(irow);
		sv   = (SchemaVariable) getValueAt(irow, 0);
                sort = null;
		if ( sv instanceof VariableSV || sv instanceof SkolemTermSV) {
		    IdDeclaration idd = parseIdDeclaration ( irow );
		    sort = idd.getSort ();
		    if ( sort == null ) {
			try {
			    sort = result.getRealSort ( sv, services );
			} catch ( SortException e ) {
			    throw new MissingSortException ( "" + sv,
							     irow, 0 );
			}
		    }
		    
		    if ( sv instanceof VariableSV ) {
		        LogicVariable lv = 
		            new LogicVariable ( new Name ( idd.getName () ),
		                    sort );
		        result = result.addCheckedInstantiation( sv, 
                                tb.var( lv ), services, true );
		    } else {
		        // sv instanceof SkolemTermSV
                        final Named n 
                        	= namespaces()
                                  .lookupLogicSymbol(new Name(idd.getName()));
                        if(n == null) { 
                            result = result.createSkolemConstant(idd.getName(),
                        	                                 sv, 
                        	                                 sort, 
                        	                                 true, 
                        	                                 services);
                        } else {
                            throw new SVInstantiationParserException(
                        	    		idd.getName(), 
                        	    		irow, 
                        	    		1, 
                        	    		"Name already in use.", 
                        	    		false);
                        }
		    }
		} else if (sv instanceof ProgramSV) {
		    final ProgramElement pe = parseRow(irow);                    
		    result = result.addCheckedInstantiation(sv, pe, services, true);
		} 
	    }
	    SchemaVariable problemVarSV = result.varSVNameConflict();

	    if (problemVarSV != null) {
		throw new SVInstantiationParserException
		    ( "", getSVRow(problemVarSV), 0,
		      "Ambiguous instantiation of schema variable " +
		      problemVarSV, false);
	    }
            	    
	    for (irow = noEditRow+1; irow < entries.size(); irow++) {

	        if ( !isInputAvailable ( irow ) )
	            continue;
	        
	        sv   = (SchemaVariable)getValueAt(irow, 0);
	        
	        if (sv instanceof VariableSV || sv instanceof SkolemTermSV ||
		    result.instantiations().isInstantiated(sv))
	            continue;
                
	        sort = null;
                
                if (sv instanceof ProgramSV) {
                    final ProgramElement pe = parseRow(irow);                    
                    result = result.addCheckedInstantiation(sv, pe, services, true);
                } else{   
                    if (isInputAvailable ( irow ) ) {
                        final Namespace extVarNS =
                            result.extendVarNamespaceForSV(nss.variables(), sv);
                        
                        Namespace functNS =
                            result.extendedFunctionNameSpace(nss.functions());
                        
                        final Term instance = parseRow(irow, extVarNS, functNS);
                        sort = instance.sort ();                    
                        
                        try {
                            result = result.addCheckedInstantiation(sv, instance, services, true);
                        } catch ( RigidnessException e ) {
                            throw new SVRigidnessException ( "" + sv, irow, 0 );
                        } catch (IllegalInstantiationException iae) {                            
                            throw new SVInstantiationParserException((String) getValueAt(irow, 1), 
								     irow, -1, iae.getMessage(), false);              
                        }                    
                    }
                }                                
	    }
	} catch ( SortException e ) {
	    throw new SortMismatchException ( "" + sv, sort, irow, 0 );
	} 

        return result;

    }

    /** sets the value of the cell */
    @Override
    public void setValueAt(Object instantiation, int rowIndex,
                           int columnIndex) {
        if (columnIndex == 0)
            entries.set(rowIndex, new Pair<>((SchemaVariable) instantiation, entries.get(rowIndex).second));
        else
            entries.set(rowIndex, new Pair<>(entries.get(rowIndex).first, (String) instantiation));
    }

    /** get value at the specified row and col
     * @return the value
     */
    @Override
    public Object getValueAt(int row, int col) {
        return  col == 0 ? entries.get(row).first : entries.get(row).second;
    }

    /** returns the index of the row the given Schemavariable stands
     *@return the index of the row the given Schemavariable stands (-1
     * if not found)
     */
    private int getSVRow(SchemaVariable sv) {
        int rowIndex = 0;
        for (Pair<SchemaVariable, String> pair: entries) {
            if (pair.first.equals(sv)) {
                return rowIndex;
            }
            ++rowIndex;
        }
        return -1;
    }

}