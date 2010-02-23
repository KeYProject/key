// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.recoderext.JMLTransformer;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.NonRigidHeapDependentFunction;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.RTSJProfile;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;

/**
 * Extracts JML class invariants and operation contracts from JML comments. 
 * This is the public interface to the jml package.
 */
public class JMLSpecExtractor implements SpecExtractor {

    private final Services services;
    private final JMLSpecFactory jsf;
    private ImmutableSet<PositionedString> warnings 
        = DefaultImmutableSet.<PositionedString>nil();

    
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
     * Concatenates the passed comments in a position-preserving way. (see also
     * JMLTransformer::concatenate(), which does the same thing for Recoder
     * ASTs)
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
        ImmutableArray<Sort> argSorts;
        try {
            sort 
                = services.getJavaInfo().getTypeByClassName(typeName).getSort();
            argSorts = decl.getMods().contains("static") 
                       ? new ImmutableArray<Sort>()
                       : new ImmutableArray<Sort>(classKjt.getSort());
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
        if(pm.getThrown() == null) {
            return "\\nothing;";
        }

        ImmutableArray<TypeReference> exceptions = pm.getThrown().getExceptions();

        if(exceptions == null) {
            return "\\nothing;";
        }

        String exceptionsString = "";

        for(int i = 0; i < exceptions.size(); i++) {
            //only subtypes of java.lang.Exception are in the default
            //signals-only
            if(services.getJavaInfo().isSubtype(
                    exceptions.get(i).getKeYJavaType(),
                    services.getJavaInfo()
                            .getKeYJavaType("java.lang.Exception"))) {
                exceptionsString 
                    += exceptions.get(i).getName() + ", ";
            }
        }

        if(exceptionsString.equals("")) {
            exceptionsString = "\\nothing";
        } else {
            //delete the last ", "
            exceptionsString 
                = exceptionsString.substring(0, exceptionsString.length() - 2);
        }
        return exceptionsString + ";";
    }

    
    /**
     * creates a JML specification expressing that the given variable/field is not null and in case of a reference
     * array type that also its elements are non-null 
     * In case of implicit fields or primitive typed fields/variables the empty set is returned 
     * @param varName the String specifying the variable/field name
     * @param kjt the KeYJavaType representing the variables/field declared type
     * @param isImplicitVar a boolean indicating if the the field is an implicit one (in which case no 
     * @param fileName the String containing the filename where the field/variable has been declared
     * @param pos the Position where to place this implicit specification
     * @return set of formulas specifying non-nullity for field/variables
     */  
    private ImmutableSet<PositionedString> createNonNullPositionedString(String varName, KeYJavaType kjt, 
	    boolean isImplicitVar, String fileName, Position pos) {
	ImmutableSet<PositionedString> result = DefaultImmutableSet.<PositionedString>nil(); 
	final Type varType  = kjt.getJavaType(); 

	if (services.getTypeConverter().isReferenceType(varType) && !isImplicitVar) {

	    PositionedString ps 
	    = new PositionedString(varName + " != null", fileName, pos);
	    result = result.add(ps);
	    if (varType instanceof ArrayType && 
		    services.getTypeConverter().
		    isReferenceType(((ArrayType)varType).getBaseType().getKeYJavaType())) {
		final PositionedString arrayElementsNonNull 
		= new PositionedString("(\\forall int i; 0 <= i && i < " + varName + ".length;" 
			+ varName + "[i]" + " != null)", 
			fileName, 
			pos);
		result = result.add(arrayElementsNonNull);
	    }
	}
	return result;
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    public ImmutableSet<ClassInvariant> extractClassInvariants(KeYJavaType kjt)
            throws SLTranslationException {
        ImmutableSet<ClassInvariant> result = DefaultImmutableSet.<ClassInvariant>nil();

        //primitive types have no class invariants
        if(!(kjt.getJavaType() instanceof TypeDeclaration)) {
            return result;
        }

        //get type declaration, file name
        TypeDeclaration td = (TypeDeclaration) kjt.getJavaType();
        String fileName = td.getPositionInfo().getFileName();

        //add invariants for non_null fields        
        for(MemberDeclaration member : td.getMembers()) {
            if (member instanceof FieldDeclaration) {
                for(FieldSpecification field : ((FieldDeclaration) member).getFieldSpecifications()) {
                    
                    //add invariant only for fields of reference types
                    //and not for implicit fields.
                    if (!JMLInfoExtractor.isNullable(field.getProgramName(), kjt)) {
                	ImmutableSet<PositionedString> nonNullInvs =
                	    createNonNullPositionedString(field.getProgramName(),
                		    field.getProgramVariable().getKeYJavaType(),
                		    field instanceof ImplicitFieldSpecification,
                		    fileName, member.getEndPosition());
                	for (PositionedString classInv : nonNullInvs) {
                	    result = result.add(jsf.createJMLClassInvariant(kjt,
                		    classInv));
                	}
                    }
                }
            }
        }

        //iterate over all children
        for(int i = 0, n = td.getChildCount(); i <= n; i++) {
            //collect comments
            //(last position are comments of type declaration itself)
            Comment[] comments = null;
            if(i < n) {
                ProgramElement child = td.getChildAt(i);
                comments = child.getComments();
                //skip model and ghost elements
                //(their comments are duplicates of other comments)
                if((child instanceof FieldDeclaration 
                       && ((FieldDeclaration) child).isGhost())
                    || (child instanceof ProgramMethod 
                        && ((ProgramMethod) child).isModel())) {
                    continue;
                }
            } else if(td.getComments() != null) {
                comments = td.getComments();
            }
            if(comments.length == 0) {
                continue;
            }

            //concatenate comments, determine position
            String concatenatedComment = concatenate(comments);
            Position pos = comments[0].getStartPosition();

            //call preparser
            KeYJMLPreParser preParser 
                = new KeYJMLPreParser(concatenatedComment, fileName, pos);
            ImmutableList<TextualJMLConstruct> constructs 
                = preParser.parseClasslevelComment();
            warnings = warnings.union(preParser.getWarnings());

            //create class invs out of textual constructs, add them to result
            for(TextualJMLConstruct c : constructs) {
                if(c instanceof TextualJMLClassInv) {
                    try {
                        TextualJMLClassInv textualInv = (TextualJMLClassInv) c;
                        ClassInvariant inv 
                            = jsf.createJMLClassInvariant(kjt, textualInv);
                        result = result.add(inv);
                    } catch (SLWarningException e) {
                        warnings = warnings.add(e.getWarning());
                    }
                } else if(c instanceof TextualJMLFieldDecl) {
                    transformFieldDecl((TextualJMLFieldDecl) c, kjt);
                }
            }
        }

        return result;
    }

    
    public ImmutableSet<OperationContract> extractOperationContracts(ProgramMethod pm)
            throws SLTranslationException {
        ImmutableSet<OperationContract> result = DefaultImmutableSet.<OperationContract>nil();

        //get type declaration, file name
        TypeDeclaration td 
            = (TypeDeclaration) pm.getContainerType().getJavaType();
        String fileName = td.getPositionInfo().getFileName();

        //determine purity, add purity contract
        final boolean isPure = JMLInfoExtractor.isPure(pm);
        if(isPure) {
            TextualJMLSpecCase sc 
                = new TextualJMLSpecCase(ImmutableSLList.<String>nil(), 
                                         Behavior.NONE);
            sc.addAssignable(new PositionedString("\\nothing"));
            ImmutableSet<OperationContract> contracts 
                = jsf.createJMLOperationContractsAndInherit(pm, sc);
            result = result.union(contracts);
        }
        
        //determine scope safety, add scope safety contract
        final boolean isScopeSafe = JMLInfoExtractor.isScopeSafe(pm) || 
            JMLInfoExtractor.isScopeSafe(pm.getContainerType());
        if(isScopeSafe) {
            TextualJMLSpecCase sc 
                = new TextualJMLSpecCase(ImmutableSLList.<String>nil(), 
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
            ImmutableSet<OperationContract> contracts
                = jsf.createJMLOperationContractsAndInherit(pm, sc);
            result = result.union(contracts);
        }

        //get textual JML constructs
        Comment[] comments = pm.getComments();
        ImmutableList<TextualJMLConstruct> constructs;
        if(comments.length != 0) {
            //concatenate comments, determine position
            String concatenatedComment = concatenate(comments);
            Position pos = comments[0].getStartPosition();
            
            //call preparser
            KeYJMLPreParser preParser 
                = new KeYJMLPreParser(concatenatedComment, fileName, pos);
            constructs = preParser.parseClasslevelComment();
            warnings = warnings.union(preParser.getWarnings());
        } else {
            constructs = ImmutableSLList.<TextualJMLConstruct>nil();
        }

        //create JML contracts out of constructs, add them to result
        TextualJMLConstruct[] constructsArray = constructs.toArray(new TextualJMLConstruct[constructs.size()]);

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

            if(isPure) {
                specCase.addDiverges(new PositionedString("false"));
                if(!pm.isConstructor()) {
                    specCase.addAssignable(new PositionedString("\\nothing"));
                } else {
                    specCase.addAssignable(new PositionedString("\\nothing"));//TODO: should be "this.*", but this is not yet supported
                }
            }
            
            if(!JMLInfoExtractor.arbitraryScopeThis(pm) && !pm.isStatic() &&
	       ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile){
                specCase.addRequires(new PositionedString("\\outerScope(\\memoryArea(this),\\currentMemoryArea)", 
                        fileName, 
                        pm.getStartPosition()));
            }
            
            //add non-null preconditions
            for(int j = 0, n = pm.getParameterDeclarationCount(); j < n; j++) {
                //no additional precondition for primitive types!
                final VariableSpecification paramDecl = pm.getParameterDeclarationAt(j)
		        .getVariableSpecification();
                if (!JMLInfoExtractor.parameterIsNullable(pm, j)) {
                    final ImmutableSet<PositionedString> nonNullParams = 
                	createNonNullPositionedString(paramDecl.getName(),
                		paramDecl.getProgramVariable().getKeYJavaType(),
                		false,
                		fileName, pm.getStartPosition());
                    for (PositionedString nonNull : nonNullParams) {
                	specCase.addRequires(nonNull);
                    }
		}
		String param_name = paramDecl.getName();
                Type t = pm.getParameterDeclarationAt(j).
                            getTypeReference().
                            getKeYJavaType();
		if(services.getTypeConverter().isReferenceType(t) &&
		   !JMLInfoExtractor.parameterInArbitraryScope(pm, j)){
		    String outerScope = "\\outerScope(\\memoryArea("+param_name+"),\\currentMemoryArea)";
		    specCase.addRequires(new PositionedString(outerScope, 
							      fileName, 
							      pm.getStartPosition()));
		}
                 
            }

            //add non-null postcondition
            KeYJavaType resultType = pm.getKeYJavaType();

            if(resultType != null &&
        	    !JMLInfoExtractor.resultIsNullable(pm) &&
        	    specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
        	final ImmutableSet<PositionedString> resultNonNull = 
        	    createNonNullPositionedString("\\result", resultType, false, 
        		    fileName, pm.getStartPosition());
        	for (PositionedString nonNull : resultNonNull) {
        	    specCase.addEnsures(nonNull);
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

            //add implicit signals-only if omitted
            if(specCase.getSignalsOnly().isEmpty()
               && specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR) {
                specCase.addSignalsOnly(
                            new PositionedString(getDefaultSignalsOnly(pm)));
            }

            //translate contract
            try {
                ImmutableSet<OperationContract> contracts 
                    = jsf.createJMLOperationContractsAndInherit(pm, specCase);
                result = result.union(contracts);
            } catch (SLWarningException e) {
                warnings = warnings.add(e.getWarning());
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
        ImmutableList<TextualJMLConstruct> constructs 
            = preParser.parseMethodlevelComment();
        warnings = warnings.union(preParser.getWarnings());

        //create JML loop invariant out of last construct
        if(constructs.size() == 0) {
            return result;
        }
        TextualJMLConstruct c = constructs.take(constructs.size() - 1).head();
        if(c instanceof TextualJMLLoopSpec) {
            try {
                TextualJMLLoopSpec textualLoopSpec = (TextualJMLLoopSpec) c;
                result = jsf.createJMLLoopInvariant(pm, loop, textualLoopSpec);
            } catch (SLWarningException e) {
                warnings = warnings.add(e.getWarning());
            }
        }

        return result;
    }

    public ImmutableSet<PositionedString> getWarnings() {
        return JMLTransformer.getWarningsOfLastInstance().union(warnings);
    }
}
