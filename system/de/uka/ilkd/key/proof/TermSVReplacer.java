// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ArrayOfVariableSpecification;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;

public class TermSVReplacer {

    Map schemaVariables;
    SetOfProgramVariable locallyDeclaredVars 
	= SetAsListOfProgramVariable.EMPTY_SET;
    SetOfProgramVariable pvsInProg 
	= SetAsListOfProgramVariable.EMPTY_SET;
    Term from, to;

    TermFactory fact;

    public TermSVReplacer(Map map) {
	fact = TermFactory.DEFAULT;
	schemaVariables = map;
    }

    private void createSV(ProgramVariable pv) {

	SortedSchemaVariable ssv = (SortedSchemaVariable)
	    SchemaVariableFactory.createProgramSV
	    (new ProgramElementName("#"+pv),
	     ProgramSVSort.VARIABLE, false);
	schemaVariables.put(pv, ssv);
    }

    public SetOfProgramVariable getLocallyDeclaredVars() {
	return locallyDeclaredVars;
    }

    public SetOfProgramVariable getPVsInProg() {
	return pvsInProg;
    }
    
    public Term inst(Term t) {
	Term result = null;
	if (t.op() instanceof ProgramVariable 
	    && !((ProgramVariable)t.op()).isMember()){ 
	    result = t;
	    if (!schemaVariables.containsKey(t.op())) {
		createSV((ProgramVariable)t.op());
	    } 
	    result = TermFactory.DEFAULT.createVariableTerm
		((SchemaVariable) schemaVariables.get(t.op()));

	} else {
	    Term subTerms[] = new Term[t.arity()];
            ArrayOfQuantifiableVariable[] quantVars = new ArrayOfQuantifiableVariable[t.arity()];
	    for ( int i = 0; i<t.arity(); i++ ) {
		quantVars[i] = t.varsBoundHere(i);		
		subTerms[i] = inst(t.sub(i));
	    }
	    Operator op;
	    if(t.op() instanceof IUpdateOperator){
		IUpdateOperator uo = (IUpdateOperator) t.op();
		ListOfLocation locs = SLListOfLocation.EMPTY_LIST;
		for(int i = 0; i<uo.locationCount(); i++){
		    if (uo.location(i) instanceof ProgramVariable 
			&& !((ProgramVariable) uo.location(i)).isMember()){ 
			if (!schemaVariables.containsKey(uo.location(i))) {
			    createSV((ProgramVariable) uo.location(i));
			} 
			locs = locs.append((Location)
					   schemaVariables.
					   get(uo.location(i)));
		    }else{
			locs = locs.append(uo.location(i));
		    }
		}
		op = uo.replaceLocations ( locs.toArray () );
	    }else{
		op = t.op();
	    }
            JavaBlock jb = t.javaBlock();
	    if (!jb.isEmpty()) {
		jb = JavaBlock.createJavaBlock
		    ((StatementBlock)inst((Statement)t.javaBlock().program()));
		if (jb.equals(t.javaBlock())) jb = t.javaBlock();
	    }
	    result = fact.createTerm(op,subTerms,quantVars,jb);	   
	}
	return result;
    }

    public Statement inst(Statement sta) {
	ProgVarReplaceVisitor pvrepl = new ProgVarReplaceVisitor
	    (sta, schemaVariables) {

		protected void walk(ProgramElement node) {
		    if (node instanceof LocalVariableDeclaration 
			&& replaceallbynew) {
			LocalVariableDeclaration vd
			    = (LocalVariableDeclaration)node;
			ArrayOfVariableSpecification vspecs
			    =vd.getVariableSpecifications();
			for (int i=0; i<vspecs.size(); i++) {
			    ProgramVariable pv 
				= (ProgramVariable) 
				vspecs.getVariableSpecification(i)
				.getProgramVariable();
			    if (!replaceMap.containsKey(pv)){
				createSV(pv);
			    }
			    locallyDeclaredVars = locallyDeclaredVars.add(pv);
			}
		    }
		    super.walk(node);
		}

		public void performActionOnProgramVariable(ProgramVariable pv) {
		    if (!pv.isMember() && !replaceMap.containsKey(pv)) {
			createSV(pv);
		    }
		    pvsInProg = pvsInProg.add(pv);
		    super.performActionOnProgramVariable(pv);
		}		
	    };

	pvrepl.start();
	return (Statement) pvrepl.result();
    }

}

