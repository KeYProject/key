//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.reference.ArrayOfTypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.NonRigidHeapDependentFunction;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.RTSJProfile;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Extracts JML class invariants and operation contracts from JML comments.
 * This is the public interface to the jml package. 
 */
public class JMLSpecExtractor implements SpecExtractor {
    
    private final Services services;
    private final JMLSpecFactory jsf;

    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public JMLSpecExtractor(Services services) {
        this.services = services;
        this.jsf = new JMLSpecFactory(services);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Concatenates the passed comments in a position-preserving way.
     * (see also JMLTransformer::concatenate(), which does the same thing
     *  for Recoder ASTs)
     */ 
    private String concatenate(Comment[] comments) {
        if(comments.length == 0) {
            return "";
        }        
        StringBuffer sb = new StringBuffer(comments[0].getText());
        
        for(int i = 1; i < comments.length; i++) {
            Position relativePos = comments[i].getRelativePosition();
            for(int j = 0; j < relativePos.getLine(); j++) {
                sb.append("\n");
            }
            for(int j = 0; j < relativePos.getColumn(); j++) {
                sb.append(" ");
            }
            sb.append(comments[i].getText());
        }
        
        return sb.toString();
    }
    
    
    private int getIndexOfMethodDecl(ProgramMethod pm, 
                                     TextualJMLConstruct[] constructsArray) {
        for(int i = 0; i < constructsArray.length; i++) {
            if(constructsArray[i] instanceof TextualJMLMethodDecl) {
                TextualJMLMethodDecl methodDecl 
                    = (TextualJMLMethodDecl) constructsArray[i];
                if(methodDecl.getMethodName().equals(pm.getName())) {
                    return i;
                }
            }
        }
        return -1;
    }
    
    
    private void transformFieldDecl(TextualJMLFieldDecl decl, 
                                    KeYJavaType classKjt) 
            throws SLTranslationException {
        if(!decl.getMods().contains("model")) {
            return;
        }
        
        String[] splittedDecl = decl.getDecl().text.split(" ");
        if(splittedDecl.length != 2) {
            throw new SLTranslationException(
                        "Unexpected structure of model field declaration!",
                        decl.getDecl().fileName,
                        decl.getDecl().pos);
        }
        String typeName  = splittedDecl[0];
        String fieldName = splittedDecl[1].substring(0, 
                                                     splittedDecl[1].length() 
                                                         - 1);
        
        Sort sort;
        ArrayOfSort argSorts;
        try {
            sort 
                = services.getJavaInfo().getTypeByClassName(typeName).getSort();
            argSorts = decl.getMods().contains("static")
                       ? new ArrayOfSort()
                       : new ArrayOfSort(classKjt.getSort());
        } catch(Throwable e) {
            throw new SLTranslationException(e.getMessage()
                                             + " (" 
                                             + e.getClass().getName() 
                                             + ")",                                              
                                             decl.getDecl().fileName, 
                                             decl.getDecl().pos,
                                             e.getStackTrace());
        }
                                   
        NonRigidHeapDependentFunction f
            = new NonRigidHeapDependentFunction(new Name(fieldName), 
                                                sort, 
                                                argSorts);
        services.getNamespaces().functions().add(f);
    }
    
    
    private String getDefaultSignalsOnly(ProgramMethod pm) {

        if (pm.getThrown() == null) {
            return "\\nothing;";
        }
        
        ArrayOfTypeReference exceptions = pm.getThrown().getExceptions();

        if (exceptions == null) {
            return "\\nothing;";
        }
        
        String exceptionsString = "";

        for (int i = 0; i < exceptions.size(); i++) {
            //only subtypes of java.lang.Exception are in the default
            //signals-only
            if (services.getJavaInfo().isSubtype(
                    exceptions.getTypeReference(i).getKeYJavaType(),
                    services.getJavaInfo()
                            .getKeYJavaType("java.lang.Exception"))) {
                exceptionsString += exceptions.getTypeReference(i).getName()
                        + ", ";
            }
        }

        if (exceptionsString.equals("")) {
            exceptionsString = "\\nothing";
        } else {
            //delete the last ", "
            exceptionsString = exceptionsString.substring(0, exceptionsString
                    .length() - 2);
        }
        return exceptionsString + ";";
    }


    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public SetOfClassInvariant extractClassInvariants(KeYJavaType kjt) 
            throws SLTranslationException {
        SetOfClassInvariant result = SetAsListOfClassInvariant.EMPTY_SET;

        //primitive types have no class invariants
        if(!(kjt.getJavaType() instanceof TypeDeclaration)) {
            return result;
        }
        
        //get type declaration, file name
        TypeDeclaration td = (TypeDeclaration) kjt.getJavaType();
        String fileName = td.getPositionInfo().getFileName();
                
        //add invariants for non_null fields
        ArrayOfMemberDeclaration fds = td.getMembers();
        for(int i = 0, m = fds.size(); i < m; i++) {            
            if(fds.getMemberDeclaration(i) instanceof FieldDeclaration) {
        	FieldDeclaration fd 
        		= (FieldDeclaration) fds.getMemberDeclaration(i);
        	ArrayOfFieldSpecification fields = fd.getFieldSpecifications();
        	for(int j = 0, n = fields.size(); j < n; j++) {
        	    FieldSpecification field = fields.getFieldSpecification(j);
                    String fieldName = field.getProgramName();
                    // add invariant only for fields of reference types
                    // and not for implicit fields.
                    // [TODO] is there a better way to check this?
                    if(services.getTypeConverter().isReferenceType(field.getType())
                            && !fieldName.startsWith("<")) {
                        if(!JMLInfoExtractor.isNullable(fieldName, kjt)) {
                            PositionedString ps 
                                = new PositionedString(fieldName + " != null", 
                                                       fileName,
                                                       fd.getEndPosition());
                            result = result.add(jsf.createJMLClassInvariant(kjt, ps));
                        }
                    }        	    
        	}
            }
        }
        
        //iterate over all children
        for(int i = 0, n = td.getChildCount(); i < n; i++) {
            ProgramElement child = td.getChildAt(i);
            Comment[] comments = child.getComments();
            if(comments.length == 0) {
                continue;
            }
            
            //skip model and ghost elements 
            //(their comments are duplicates of other comments)
            if((child instanceof FieldDeclaration
                    && ((FieldDeclaration) child).isGhost())
                || (child instanceof ProgramMethod
                    && ((ProgramMethod) child).isModel())) {
                continue;
            }
            
            //concatenate comments, determine position
            String concatenatedComment = concatenate(comments);
            Position pos = comments[0].getStartPosition();
            
            //call preparser
            KeYJMLPreParser preParser 
                = new KeYJMLPreParser(concatenatedComment, fileName, pos);
            ListOfTextualJMLConstruct constructs 
                = preParser.parseClasslevelComment();
            
            //create class invs out of textual constructs, add them to result
            for(IteratorOfTextualJMLConstruct it = constructs.iterator(); 
                it.hasNext(); ) {
                TextualJMLConstruct c = it.next();
                if(c instanceof TextualJMLClassInv) {
                    TextualJMLClassInv textualInv = (TextualJMLClassInv) c;
                    ClassInvariant inv 
                        = jsf.createJMLClassInvariant(kjt, textualInv);
                    result = result.add(inv);
                } else if(c instanceof TextualJMLFieldDecl) {
                    transformFieldDecl((TextualJMLFieldDecl)c, kjt);
                }
            }            
        }

        return result; 
    }
    

    public SetOfOperationContract extractOperationContracts(ProgramMethod pm) 
            throws SLTranslationException {
        SetOfOperationContract result = SetAsListOfOperationContract.EMPTY_SET;
        
        //get type declaration, file name
        TypeDeclaration td 
            = (TypeDeclaration) pm.getContainerType().getJavaType();
        String fileName = td.getPositionInfo().getFileName();

        //determine purity, add purity contract
        final boolean isPure = JMLInfoExtractor.isPure(pm);
        if(isPure) {
            TextualJMLSpecCase sc 
            	= new TextualJMLSpecCase(SLListOfString.EMPTY_LIST, 
                                     	 Behavior.NONE);
            sc.addAssignable(new PositionedString("\\nothing"));
            SetOfOperationContract contracts
            	= jsf.createJMLOperationContractsAndInherit(pm, sc);
            result = result.union(contracts);
        }
        
        //determine scope safety, add scope safety contract
        final boolean isScopeSafe = JMLInfoExtractor.isScopeSafe(pm) || 
            JMLInfoExtractor.isScopeSafe(pm.getContainerType());
        if(isScopeSafe) {
            TextualJMLSpecCase sc 
                = new TextualJMLSpecCase(SLListOfString.EMPTY_LIST, 
                                         Behavior.BEHAVIOR);
/*            if(pm.getKeYJavaType()!=null && 
                    !(pm.getKeYJavaType().getSort() instanceof PrimitiveSort)){
                sc.addEnsures(new PositionedString("\\result!=null ==> \\inImmortalMemory(\\result)"));
            }*/
	    //            sc.addDiverges(new PositionedString("true"));
            sc.addSignals(new PositionedString("(Throwable e) !(e instanceof javax.realtime.IllegalAssignmentError || "+
                    "e instanceof javax.realtime.ScopedCycleException || "+
                    "e instanceof javax.realtime.InaccessibleAreaException ||"+
                    "e instanceof javax.realtime.ThrowBoundaryError)"));
            SetOfOperationContract contracts
                = jsf.createJMLOperationContractsAndInherit(pm, sc);
            result = result.union(contracts);
        }

        //get textual JML constructs
        Comment[] comments = pm.getComments();        
        ListOfTextualJMLConstruct constructs;
        if (comments.length != 0) {
            //concatenate comments, determine position
            String concatenatedComment = concatenate(comments);
            Position pos = comments[0].getStartPosition();
            //call preparser
            KeYJMLPreParser preParser 
                = new KeYJMLPreParser(concatenatedComment, fileName, pos);
            constructs = preParser.parseClasslevelComment();
        } else {
            constructs = SLListOfTextualJMLConstruct.EMPTY_LIST;
        }
        
        //create JML contracts out of constructs, add them to result
        TextualJMLConstruct[] constructsArray = constructs.toArray();
        
        int startPos;
        if(pm.isModel()) {
            startPos = getIndexOfMethodDecl(pm, constructsArray) - 1;
            assert startPos != constructsArray.length - 1;
        } else {
            startPos = constructsArray.length - 1;
        }
        for(int i = startPos; 
            i >= 0 && constructsArray[i] instanceof TextualJMLSpecCase;
            i--) {
            TextualJMLSpecCase specCase 
                = (TextualJMLSpecCase) constructsArray[i];
            
            if (isPure) {
                specCase.addDiverges(new PositionedString("false"));
                if (!pm.isConstructor()) {
                    specCase.addAssignable(new PositionedString("\\nothing"));
                } else {
                    specCase.addAssignable(new PositionedString("this.*"));
                }
            }
            
            if(!JMLInfoExtractor.arbitraryScopeThis(pm) && !pm.isStatic()){
                specCase.addRequires(new PositionedString("\\outerScope(\\memoryArea(this),\\currentMemoryArea)", 
                        fileName, 
                        pm.getStartPosition()));
            }
            
            //add non-null and outer scope preconditions
            for (int j = 0, n = pm.getParameterDeclarationCount(); j < n; j++) {
                Type t = pm.getParameterDeclarationAt(j).
                            getTypeReference().
                            getKeYJavaType();
                // no additional precondition for primitive types!
                if (services.getTypeConverter().isReferenceType(t)){
                    String param_name = pm.
                        getParameterDeclarationAt(j).
                        getVariableSpecification().
                        getName();
                    if(!JMLInfoExtractor.parameterIsNullable(pm, j)) {
                        String nonNull = param_name + " != null";
                        specCase.addRequires(new PositionedString(
                               nonNull, 
                               fileName, 
                               pm.getStartPosition()));
                   }
                   if(!JMLInfoExtractor.parameterInArbitraryScope(pm, j)){
                       String outerScope = "\\outerScope(\\memoryArea("+param_name+"),\\currentMemoryArea)";
                       specCase.addRequires(new PositionedString(
                               outerScope, 
                               fileName, 
                               pm.getStartPosition()));
                   }
                }
                 
            }
            
            //add non-null postcondition
            KeYJavaType resultType = pm.getKeYJavaType();
            if(resultType != null
               && services.getTypeConverter().isReferenceType(resultType)
               && specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                if(!JMLInfoExtractor.resultIsNullable(pm)){
                    String nonNull = "\\result " + " != null";
                    specCase.addEnsures(new PositionedString(
                            nonNull, 
                            fileName, 
                            pm.getStartPosition()));
                }
                if(!JMLInfoExtractor.resultArbitraryScope(pm) &&
                        ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile){
                    String outerScope = "\\outerScope(\\memoryArea(\\result),\\currentMemoryArea)";
                    specCase.addEnsures(new PositionedString(
                            outerScope, 
                            fileName, 
                            pm.getStartPosition()));            
                }
            }
            
            // add implicit signals-only if omitted
            if (specCase.getSignalsOnly().isEmpty()
                    && specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR) {
                specCase.addSignalsOnly(new PositionedString(
                        getDefaultSignalsOnly(pm)));
            }
            
            SetOfOperationContract contracts 
                = jsf.createJMLOperationContractsAndInherit(pm, specCase);
            result = result.union(contracts);
        }
        
        return result;          
    }
    
    
    public LoopInvariant extractLoopInvariant(ProgramMethod pm, 
                                              LoopStatement loop) 
            throws SLTranslationException {
        LoopInvariant result = null;
        
        //get type declaration, file name
        TypeDeclaration td 
            = (TypeDeclaration) pm.getContainerType().getJavaType();
        String fileName = td.getPositionInfo().getFileName();
        
        //get comments
        Comment[] comments = loop.getComments();
        if(comments.length == 0) {
            return result;
        }
        
        //concatenate comments, determine position
        String concatenatedComment = concatenate(comments);
        Position pos = comments[0].getStartPosition();
        
        //call preparser
        KeYJMLPreParser preParser 
            = new KeYJMLPreParser(concatenatedComment, fileName, pos);
        ListOfTextualJMLConstruct constructs 
            = preParser.parseMethodlevelComment();
        
        //create JML loop invariant out of last construct
        if(constructs.size() == 0) {
            return result;
        }
        TextualJMLConstruct c = constructs.take(constructs.size() - 1).head();
        if(c instanceof TextualJMLLoopSpec) {
            TextualJMLLoopSpec textualLoopSpec = (TextualJMLLoopSpec) c;
            result = jsf.createJMLLoopInvariant(pm, loop, textualLoopSpec);
        }
        
        return result;
    }
}
