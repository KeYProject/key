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

package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.ImplicitFieldSpecification;
import de.uka.ilkd.key.java.declaration.MemberDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.recoderext.JMLTransformer;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.KeYJMLPreParser;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassAxiom;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassInv;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLDepends;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLInitially;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLRepresents;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;

import java.util.*;

/**
 * Extracts JML class invariants and operation contracts from JML comments.
 * This is the public interface to the jml package. Note that internally,
 * this class is highly similar to the class java.recoderext.JMLTransformer;
 * if you change one of these classes, you probably need to change the other
 * as well.
 */
public final class JMLSpecExtractor implements SpecExtractor {

    private static final String THROWABLE = "java.lang.Throwable";
    private static final String ERROR = "java.lang.Error";
    private static final String RUNTIME_EXCEPTION = "java.lang.RuntimeException";
    private static final String DEFAULT_SIGNALS_ONLY = "signals_only "+ERROR+", "+RUNTIME_EXCEPTION+";";
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


    private int getIndexOfMethodDecl(IProgramMethod pm,
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



    // includes unchecked exceptions (instances of Error or RuntimeException)
    // (see resolution to issue #1379)
    private String getDefaultSignalsOnly(IProgramMethod pm) {
        if(pm.getThrown() == null) {
            return DEFAULT_SIGNALS_ONLY;
        }

        ImmutableArray<TypeReference> exceptions = pm.getThrown().getExceptions();

        if(exceptions == null) {
            return DEFAULT_SIGNALS_ONLY;
        }

        String exceptionsString = ERROR +", " + RUNTIME_EXCEPTION + ", ";

        for(int i = 0; i < exceptions.size(); i++) {
            if(services.getJavaInfo().isSubtype(
                    exceptions.get(i).getKeYJavaType(),
                    services.getJavaInfo()
                            .getKeYJavaType(THROWABLE))) {
                exceptionsString
                    += exceptions.get(i).getKeYJavaType().getFullName() + ", ";
            }
        }

        if(exceptionsString.equals("")) {
            exceptionsString = "\\nothing";
        } else {
            //delete the last ", "
            exceptionsString
                = exceptionsString.substring(0, exceptionsString.length() - 2);
        }
        return "signals_only " + exceptionsString + ";";
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
    public static ImmutableSet<PositionedString>
                        createNonNullPositionedString(String varName,KeYJavaType kjt,
                                                      boolean isImplicitVar, String fileName,
                                                      Position pos, Services services) {
        ImmutableSet<PositionedString> result = DefaultImmutableSet.<PositionedString>nil();
        final Type varType  = kjt.getJavaType();

        final TypeConverter typeConverter = services.getTypeConverter();
        if (typeConverter.isReferenceType(varType) && !isImplicitVar) {
            final int arrayDepth = arrayDepth(varType, services);

            // use special "deep" non null predicate (see bug #1392)
            // ... looks a bit like a hack with those DL escapes ...
            final String nonNullString = arrayDepth > 0 ?
                    "\\dl_nonNull(\\dl_heap(),"+varName+","+arrayDepth+")" : varName+" != null";
            PositionedString ps = new PositionedString(nonNullString, fileName, pos)
                    .label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL);
            result = result.add(ps);
        }
        return result;
    }
    
    /**
     * Get the depth for the nonNull predicate.
     * The depth is 0 for non array types,
     * its dimension for reference array types,
     * and its dimension -1 for array types with primitive base type.
     */
    public static int arrayDepth (Type type, Services services) {
        assert services != null;
        final TypeConverter tc = services.getTypeConverter();
        if (type instanceof ArrayType) {
            final int d = ((ArrayType)type).getDimension();
            while (type instanceof ArrayType) {
                type = ((ArrayType)type).getBaseType().getKeYJavaType().getJavaType();
            }
            return tc.isReferenceType(type)? d: d-1;
        } else return 0;
    }


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public ImmutableSet<SpecificationElement> extractClassSpecs(KeYJavaType kjt)
            throws SLTranslationException {
        ImmutableSet<SpecificationElement> result
        	= DefaultImmutableSet.<SpecificationElement>nil();

        //primitive types have no class invariants
        if(!(kjt.getJavaType() instanceof TypeDeclaration)) {
            return result;
        }

        //get type declaration, file name
        TypeDeclaration td = (TypeDeclaration) kjt.getJavaType();
        String fileName = td.getPositionInfo().getFileName();

        //add invariants for non_null fields
        for(MemberDeclaration member : td.getMembers()) {
            if(member instanceof FieldDeclaration) {
                VisibilityModifier visibility = null;
                for(Modifier mod : member.getModifiers()) {
                    if(mod instanceof VisibilityModifier) {
                        visibility = (VisibilityModifier)mod;
                        break;
                    }
                }
                // check for spec_* modifiers (bug #1280)
                if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration)member, "spec_public"))
                    visibility = new Public();
                else if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration)member, "spec_protected"))
                    visibility = new Protected();


                for(FieldSpecification field
                      : ((FieldDeclaration) member).getFieldSpecifications()) {
                    // add a static invariant for static fields
                    boolean isStatic = member.isStatic();

                    //add invariant only for fields of reference types
                    //and not for implicit fields.
                    if(!JMLInfoExtractor.isNullable(field.getProgramName(), kjt)) {
                	ImmutableSet<PositionedString> nonNullInvs =
                	    createNonNullPositionedString(field.getProgramName(),
                		    field.getProgramVariable().getKeYJavaType(),
                		    field instanceof ImplicitFieldSpecification,
                                    fileName, member.getEndPosition(), services);
                	for(PositionedString classInv : nonNullInvs) {
                            result = result.add(
                                    jsf.createJMLClassInvariant(
                                            kjt, visibility, isStatic,
                                            classInv.label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL)));
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
                       && (((FieldDeclaration) child).isGhost()
                           || ((FieldDeclaration) child).isModel()))
                    || (child instanceof IProgramMethod
                        && ((IProgramMethod) child).isModel())) {
                    continue;
                }
            } else if(td.getComments() != null) {
                comments = td.getComments();
            }
            if(comments == null || comments.length == 0) {
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
        	try {
        	    if(c instanceof TextualJMLClassInv) {
        		TextualJMLClassInv textualInv = (TextualJMLClassInv) c;
        		ClassInvariant inv
        			= jsf.createJMLClassInvariant(kjt, textualInv);
        		result = result.add(inv);
        	    } else if(c instanceof TextualJMLInitially) {
        	        TextualJMLInitially textualRep = (TextualJMLInitially) c;
        	        InitiallyClause inc = jsf.createJMLInitiallyClause(kjt, textualRep);
        	        result = result.add(inc);
        	    } else if(c instanceof TextualJMLRepresents) {
        		TextualJMLRepresents textualRep = (TextualJMLRepresents) c;
        		ClassAxiom rep
        			= jsf.createJMLRepresents(kjt, textualRep);
        		result = result.add(rep);
        	    } else if(c instanceof TextualJMLDepends) {
        		TextualJMLDepends textualDep = (TextualJMLDepends) c;
        		Contract depContract
        			= jsf.createJMLDependencyContract(kjt, textualDep);
        		result = result.add(depContract);
        	    } else if (c instanceof TextualJMLClassAxiom){
        		ClassAxiom ax = jsf.createJMLClassAxiom(kjt, (TextualJMLClassAxiom)c);
        		result = result.add(ax);
        	    } else {
        	        // DO NOTHING
                        // There may be other kinds of JML constructs which are not specifications.
        	    }
        	} catch (SLWarningException e) {
        	    warnings = warnings.add(e.getWarning());
        	}
            }
        }

        return result;
    }


    @Override
    public ImmutableSet<SpecificationElement> extractMethodSpecs(IProgramMethod pm)
    throws SLTranslationException {
        return extractMethodSpecs(pm,true);
    }

    /**
     * Extracts method specifications (i.e., contracts) from Java+JML input.
     * @param pm method to extract for
     * @param addInvariant whether to add <i>static</i> invariants to pre- and post-conditions
     */
    @Override
    public ImmutableSet<SpecificationElement> extractMethodSpecs(IProgramMethod pm,
                                                                 boolean addInvariant)
                  throws SLTranslationException {
        ImmutableSet<SpecificationElement> result
        = DefaultImmutableSet.<SpecificationElement>nil();

        //get type declaration, file name
        TypeDeclaration td
        = (TypeDeclaration) pm.getContainerType().getJavaType();
        String fileName = td.getPositionInfo().getFileName();

        //determine purity
        final boolean isStrictlyPure = JMLInfoExtractor.isStrictlyPure(pm);
        final boolean isPure = JMLInfoExtractor.isPure(pm);
        final boolean isHelper = JMLInfoExtractor.isHelper(pm);

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
        TextualJMLConstruct[] constructsArray
        = constructs.toArray(new TextualJMLConstruct[constructs.size()]);

        int startPos;
        TextualJMLMethodDecl modelMethodDecl = null;
        if(pm.isModel()) {
            startPos = getIndexOfMethodDecl(pm, constructsArray) - 1;
            modelMethodDecl = (TextualJMLMethodDecl)constructsArray[startPos+1];
            if(startPos < 0 || !(constructsArray[startPos] instanceof TextualJMLSpecCase)) {
              //Special case, the method is model, but does not have any specification
              //create an empty one and insert it:
              TextualJMLSpecCase modelSpec = new TextualJMLSpecCase(
                 ImmutableSLList.<String>nil(),
                 Behavior.NORMAL_BEHAVIOR);
              TextualJMLConstruct[] t = new TextualJMLConstruct[constructsArray.length+1];
              startPos++;
              System.arraycopy(constructsArray, 0, t, 0, startPos);
              System.arraycopy(constructsArray, startPos, t, startPos+1,
                               constructsArray.length - startPos);
              t[startPos] = modelSpec;
              constructsArray = t;
            }
            assert startPos != constructsArray.length - 1;
        } else {
            startPos = constructsArray.length - 1;
        }
        for(int i = startPos;
        i >= 0 && constructsArray[i] instanceof TextualJMLSpecCase;
        i--) {
            TextualJMLSpecCase specCase
            = (TextualJMLSpecCase) constructsArray[i];
            if(modelMethodDecl != null && modelMethodDecl.getMethodDefinition() != null) {
               specCase.addAxioms(modelMethodDecl.getMethodDefinition());
            }

            //add purity. Strict purity overrides purity.
            if(isStrictlyPure || pm.isModel()) {
                specCase.addAssignable(new PositionedString("assignable \\strictly_nothing"));
            } else if(isPure) {
                specCase.addAssignable(new PositionedString("assignable \\nothing"));
            }

            //add invariants
            if(!isHelper && pm.getStateCount() > 0 && (!pm.isStatic() || addInvariant)) {
                // for a static method translate \inv once again, otherwise use the internal symbol
                final String invString = pm.isStatic()? "\\inv": "<inv>";
                if(!pm.isConstructor()) {
                    specCase.addRequires(new PositionedString(invString)
                                 .label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL));
                } else if (addInvariant) {
                    // add static invariant to constructor's precondition
                    specCase.addRequires(new PositionedString(""+pm.getName()+".\\inv")
                                                .label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL));
                }
                if(specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                    specCase.addEnsures(new PositionedString("ensures "+invString)
                                           .label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL));
                }
                if(specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR && !pm.isModel()) {
                    specCase.addSignals(new PositionedString("signals (Throwable e) "+invString)
                                                         .label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL));
                }
            }

            //add non-null preconditions
            for(int j = 0, n = pm.getParameterDeclarationCount(); j < n; j++) {
                final VariableSpecification paramDecl =
                        pm.getParameterDeclarationAt(j).getVariableSpecification();
                if (!JMLInfoExtractor.parameterIsNullable(pm, j)) {
                    //no additional precondition for primitive types! createNonNullPos... takes care of that
                    final ImmutableSet<PositionedString> nonNullParams =
                        createNonNullPositionedString(paramDecl.getName(),
                                paramDecl.getProgramVariable().getKeYJavaType(),
                                false, fileName, pm.getStartPosition(), services);
                    for (PositionedString nonNull : nonNullParams) {
                        specCase.addRequires(nonNull.label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL));
                    }
                }
            }

            //add non-null postcondition
            KeYJavaType resultType = pm.getReturnType();

            if(!pm.isVoid() && !pm.isConstructor() &&
                    !JMLInfoExtractor.resultIsNullable(pm) &&
                    specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                final ImmutableSet<PositionedString> resultNonNull =
                    createNonNullPositionedString("\\result", resultType,
                            false, fileName, pm.getStartPosition(), services);
                for (PositionedString nonNull : resultNonNull) {
                    specCase.addEnsures(
                            nonNull.prepend("ensures ").label(ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL));
                }
            }

            //add implicit signals-only if omitted
            if(specCase.getSignalsOnly().isEmpty()
                    && specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR
                    && !pm.isModel()) {
                specCase.addSignalsOnly(new PositionedString(getDefaultSignalsOnly(pm)));
            }

            //translate contract
            try {
                ImmutableSet<Contract> contracts
                = jsf.createJMLOperationContracts(pm, specCase);
                for(Contract contract : contracts) {
                    result = result.add(contract);
                }
            } catch (SLWarningException e) {
                warnings = warnings.add(e.getWarning());
            }
        }

        return result;
    }


    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method, final StatementBlock block) throws SLTranslationException
    {
        return createBlockContracts(method, new LinkedList<Label>(), block, block.getComments());
    }

    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method, final LabeledStatement labeled) throws SLTranslationException
    {
        final List<Label> labels = new LinkedList<Label>();
        labels.add(labeled.getLabel());
        Statement nextNonLabeled = labeled.getBody();
        while (nextNonLabeled instanceof LabeledStatement) {
            final LabeledStatement currentLabeled = (LabeledStatement) nextNonLabeled;
            labels.add(currentLabeled.getLabel());
            nextNonLabeled = currentLabeled.getBody();
        }
        if (nextNonLabeled instanceof StatementBlock) {
            return createBlockContracts(method, labels, (StatementBlock) nextNonLabeled, labeled.getComments());
        }
        else {
            return DefaultImmutableSet.nil();
        }
    }

    private ImmutableSet<BlockContract> createBlockContracts(final IProgramMethod method,
                                                             final List<Label> labels,
                                                             final StatementBlock block,
                                                             final Comment[] comments)
            throws SLTranslationException
    {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        // For some odd reason every comment block appears twice; thus we remove duplicates.
        final TextualJMLConstruct[] constructs = parseMethodLevelComments(removeDuplicates(comments), getFileName(method));
        for (int i = constructs.length - 1; i >= 0 && constructs[i] instanceof TextualJMLSpecCase; i--) {
            final TextualJMLSpecCase specificationCase = (TextualJMLSpecCase) constructs[i];
            try {
                result = result.union(jsf.createJMLBlockContracts(method, labels, block, specificationCase));
            }
            catch (final SLWarningException exception) {
                warnings = warnings.add(exception.getWarning());
            }
        }
        return result;
    }

    private String getFileName(final IProgramMethod method) {
        final TypeDeclaration type = (TypeDeclaration) method.getContainerType().getJavaType();
        return type.getPositionInfo().getFileName();
    }

    private TextualJMLConstruct[] parseMethodLevelComments(final Comment[] comments, final String fileName) throws SLTranslationException {
        if (comments.length == 0) {
            return new TextualJMLConstruct[0];
        }
        final String concatenatedComment = concatenate(comments);
        final Position position = comments[0].getStartPosition();
        final KeYJMLPreParser preParser = new KeYJMLPreParser(concatenatedComment, fileName, position);
        final ImmutableList<TextualJMLConstruct> constructs = preParser.parseMethodlevelComment();
        warnings = warnings.union(preParser.getWarnings());
        return constructs.toArray(new TextualJMLConstruct[constructs.size()]);
    }

    private Comment[] removeDuplicates(final Comment[] comments) {
        final Set<Comment> uniqueComments = new LinkedHashSet<Comment>(Arrays.asList(comments));
        return uniqueComments.toArray(new Comment[uniqueComments.size()]);
    }


    @Override
    public LoopInvariant extractLoopInvariant(IProgramMethod pm,
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


    @Override
    public ImmutableSet<PositionedString> getWarnings() {
        return JMLTransformer.getWarningsOfLastInstance().union(warnings);
    }
}