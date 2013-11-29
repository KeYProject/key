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


package de.uka.ilkd.key.proof;

import java.io.StringReader;
import java.util.Iterator;
import java.util.Vector;

import javax.swing.table.AbstractTableModel;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.rule.NewVarcond;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.*;


public class TacletInstantiationsTableModel extends AbstractTableModel {

    /**
     * 
     */
    private static final long serialVersionUID = 5285420522875326156L;
    /** the instantiations entries */
    private Vector<Object[]> entries;
    /** the related rule application */
    private final TacletApp originalApp;
    /** the integer defines the row until which no editing is possible */
    private int noEditRow;
    /** universal namespace of variables, minimum for input in a row */
    private NamespaceSet nss;
    /** the java service object */
    private Services services;
    /** the abbreviationmap */
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
    public TacletInstantiationsTableModel(TacletApp    app, 
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
    public NamespaceSet namespaces() {
        return nss;
    }

    /** creates a Vector with the row entries of the table
    */
    private Vector<Object[]> createEntryArray(TacletApp tacletApp) {
        Vector<Object[]> rowVec = new Vector<Object[]>();
        Iterator<SchemaVariable> it = tacletApp.instantiations().svIterator();
        int count = 0;

        while (it.hasNext()) {
            SchemaVariable sv = it.next();
            Object[] column = new Object[2];
            column[0] = sv;
            column[1] = ProofSaver.printAnything(
	        tacletApp.instantiations().getInstantiation(sv), 
                services);
            rowVec.add(column);
            count++;
        }

        noEditRow = count - 1;

        Iterator<SchemaVariable> varIt = tacletApp.uninstantiatedVars().iterator();
        ImmutableList<String> proposals = ImmutableSLList.<String>nil();

        while (varIt.hasNext()) {
            Object[] column = new Object[2];
            SchemaVariable var = varIt.next();

            if (!tacletApp.taclet ().getIfFindVariables ().contains(var)) {
                column[0] = var;

                // create an appropriate and unique proposal for the name ...
                String proposal
                        = instantiationProposers.getProposal(tacletApp,
                                                             var,
                                                             services,
                                                             goal.node(),
                                                             proposals);

                if(proposal != null) {
                    // A proposal is available ...
                    column[1] = proposal;
                    proposals = proposals.append(proposal);
                }

                rowVec.add(column);
            }
        }

        return rowVec;
    }


    /** adds an instantiation of a schemavariable */
    public void addInstantiationEntry(int row, Term instantiation) {
	entries.get(row)[1] = instantiation;
    }

    /** return the rule application which is the table models base
     *  @return the Ruleapp
     */
    public TacletApp application() {
        return originalApp;
    }

    /** number of colums
     * @return number of colums
     */
    public int getColumnCount() {
        return 2;
    }

    /** number of rows
     * @return number of rows
     */
    public int getRowCount() {
        return entries.size();
    }

    /** returns true iff an instantiation is missing
     * @return true iff an instantiation is missing
     */
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
    public Term parseTerm(String s, Namespace varNS, Namespace functNS)
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
    public IdDeclaration parseIdDeclaration ( String s )
        throws ParserException {
        try {
            KeYParser parser =
                new KeYParser (ParserMode.DECLARATION, new KeYLexer ( new StringReader ( s ),
                                 services.getExceptionHandler() ), "",
                                 services,   // should not be needed
                                 nss );
            return parser.id_declaration ();
        } catch (antlr.RecognitionException re) {
            throw new ParserException(re.getMessage(),
                                      new Location(re.getFilename(),
                                                   re.getLine(),
                                                   re.getColumn()));
        } catch (antlr.TokenStreamException tse) {
            throw new ParserException(tse.getMessage(), null);
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

    public static ProgramElement getProgramElement(TacletApp app,
						   String instantiation,
						   SchemaVariable sv,
						   Services services) {
	Sort svSort = sv.sort();
	if (svSort == ProgramSVSort.LABEL) {
	    return VariableNamer.parseName(instantiation);
	} else if (svSort == ProgramSVSort.VARIABLE ) {
	    NewVarcond nvc = app.taclet().varDeclaredNew(sv);
	    if (nvc != null) {
		KeYJavaType kjt;
		Object o = nvc.getTypeDefiningObject();
		JavaInfo javaInfo = services.getJavaInfo ();
		if (o instanceof SchemaVariable) {
	            final TypeConverter tc = services.getTypeConverter();
		    final SchemaVariable peerSV = (SchemaVariable)o;
		    final Object peerInst = app.instantiations().getInstantiation(peerSV);
                    if(peerInst instanceof TypeReference){
                        kjt = ((TypeReference) peerInst).getKeYJavaType();
                    } else {
                        Expression peerInstExpr;
                        if(peerInst instanceof Term) {
                            peerInstExpr = tc.convertToProgramElement((Term)peerInst);
                        } else {
                            peerInstExpr = (Expression)peerInst;
                        }
                        kjt = tc.getKeYJavaType(peerInstExpr, 
                        			app.instantiations().getContextInstantiation().activeStatementContext());
                    }
		} else {
		    kjt = javaInfo.getKeYJavaType((Type)o);
		}
                assert kjt != null : "could not find kjt for: " + o;
		return new LocationVariable
		    (VariableNamer.parseName(instantiation), kjt);
	    }
	}
	return null;
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


	ProgramElement pe = getProgramElement(originalApp, instantiation, sv, services);
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

        final TermBuilder tb = TermBuilder.DF;
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

    /** sets the Value of the cell */
    public void setValueAt(Object instantiation, int rowIndex,
                           int columnIndex) {
	entries.get(rowIndex)[columnIndex] = instantiation;
    }

    /** get value at the specified row and col
     * @return the value
     */
    public Object getValueAt(int row, int col) {
        return  entries.get(row)[col];
    }

    /** returns the index of the row the given Schemavariable stands
     *@return the index of the row the given Schemavariable stands (-1
     * if not found)
     */
    public int getSVRow(SchemaVariable sv) {
        for (int i = 0; i < entries.size(); i++) {
            if (getValueAt(i, 0).equals(sv)) {
                return i;
            }
        }
        return -1;
    }

}
