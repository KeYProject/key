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
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Field;
import de.uka.ilkd.key.java.abstraction.IteratorOfField;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfField;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.NonRigidHeapDependentFunction;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.speclang.PositionedString;
import de.uka.ilkd.key.speclang.SetAsListOfClassInvariant;
import de.uka.ilkd.key.speclang.SetAsListOfOperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;
import de.uka.ilkd.key.speclang.SetOfOperationContract;
import de.uka.ilkd.key.speclang.SpecExtractor;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.IteratorOfTextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.SLListOfTextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassInv;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLFieldDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec;
import de.uka.ilkd.key.speclang.jml.pretranslation.KeYJMLPreParser;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.pretranslation.ListOfTextualJMLConstruct;
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
        
        Sort sort = services.getJavaInfo().getTypeByName(typeName).getSort();
        ArrayOfSort argSorts = decl.getMods().contains("static")
                               ? new ArrayOfSort()
                               : new ArrayOfSort(classKjt.getSort());
                                   
        NonRigidHeapDependentFunction f
            = new NonRigidHeapDependentFunction(new Name(fieldName), 
                                                sort, 
                                                argSorts);
        services.getNamespaces().functions().add(f);
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
        
        //abort if library class (TODO: delete this)
        if(td.isLibraryClass()) {
            return result;
        }
        
        //add invariants for non_null fields.
        ListOfField fields = td.getAllFields(services);
        for (IteratorOfField it = fields.iterator(); it.hasNext(); ) {
            Field field = it.next();
            String fieldName = field.getProgramName();
            // add invariant only for fields of reference types
            // and not for implicit fields.
            // [TODO] is there a better way to check this?
            if (services.getTypeConverter().isReferenceType(field.getType())
                    && !fieldName.startsWith("<")) {
                if (!JMLInfoExtractor.isNullable(fieldName, kjt)) {
                    PositionedString ps 
                        = new PositionedString(fieldName + " != null", 
                                               fileName);
                    result = result.add(jsf.createJMLClassInvariant(kjt, ps));
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

        //abort if library class (TODO: delete this)
        if(td.isLibraryClass()) {
            return result;
        }        
        
        //determine purity 
        final boolean isPure = JMLInfoExtractor.isPure(pm);

        //get comments
        Comment[] comments = pm.getComments();
        if(comments.length == 0 && !isPure) {
            return result;
        }
        
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
            // method is declared pure and has no other comments
            assert isPure;
            constructs = SLListOfTextualJMLConstruct.EMPTY_LIST;
        }
        
        assert constructs != null;
        
        //if pure, add default contract
        if(isPure) {
            TextualJMLSpecCase sc 
                = new TextualJMLSpecCase(SLListOfString.EMPTY_LIST, 
                                         Behavior.NONE);
            constructs = constructs.append(sc);
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
        int i;
        if (isPure) {
            i = constructsArray.length - 1;
        } else {
            i = startPos;
        }
        while (i >= 0 && constructsArray[i] instanceof TextualJMLSpecCase) {
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
            
            //add non-null preconditions
            for (int j = 0, n = pm.getParameterDeclarationCount(); j < n; j++) {
                Type t = pm.getParameterDeclarationAt(j).
                            getTypeReference().
                            getKeYJavaType();
                boolean isReferenceType = services.getTypeConverter().
                                                 isReferenceType(t);
                // no additional precondition for primitive types!
                if (isReferenceType
                        && !JMLInfoExtractor.parameterIsNullable(pm, j)) {
                    String param_name = pm.
                            getParameterDeclarationAt(j).
                            getVariableSpecification().
                            getName();
                    String nonNull = param_name + " != null";
                    specCase.addRequires(new PositionedString(nonNull));
                }
            }
            
            //add non-null postcondition
            KeYJavaType resultType = pm.getKeYJavaType();
            if(resultType != null
               && services.getTypeConverter().isReferenceType(resultType)
               && !JMLInfoExtractor.resultIsNullable(pm)
               && specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                String nonNull = "\\result " + " != null";
                specCase.addEnsures(new PositionedString(nonNull));
            }
            
            SetOfOperationContract contracts 
                = jsf.createJMLOperationContractsAndInherit(pm, specCase);
            result = result.union(contracts);
            if (i == startPos && isPure && pm.isModel()) {
                i = getIndexOfMethodDecl(pm, constructsArray) - 1;
            } else {
                i--;
            }
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
