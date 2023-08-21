/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import java.net.URI;
import java.util.*;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Protected;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.recoderext.JMLTransformer;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import de.uka.ilkd.key.speclang.njml.PreParser;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;

import org.key_project.util.collection.*;

import org.antlr.v4.runtime.ParserRuleContext;

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.Clause.SIGNALS_ONLY;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.*;
import static java.lang.String.format;

/**
 * Extracts JML class invariants and operation contracts from JML comments. This is the public
 * interface to the jml package. Note that internally, this class is highly similar to the class
 * java.recoderext.JMLTransformer; if you change one of these classes, you probably need to change
 * the other as well.
 */
public final class JMLSpecExtractor implements SpecExtractor {
    private static final String THROWABLE = "java.lang.Throwable";
    private static final String ERROR = "java.lang.Error";
    private static final String RUNTIME_EXCEPTION = "java.lang.RuntimeException";
    /** The default signals only clause for errors and runtime exceptions. **/
    private static final String DEFAULT_SIGNALS_ONLY =
        format("signals_only %s, %s;", ERROR, RUNTIME_EXCEPTION);
    /**
     * This is the term label for implicit specification clauses. This is important for
     * well-definedness checks. Hence, do not change its usages unless you understand and have
     * thought about the semantics of the corresponding well-definedness checks.
     **/
    private static final TermLabel IMPL_TERM_LABEL =
        ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL;
    private final Services services;
    private final JMLSpecFactory jsf;
    private ImmutableList<PositionedString> warnings = ImmutableSLList.nil();

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public JMLSpecExtractor(Services services) {
        this.services = services;
        this.jsf = new JMLSpecFactory(services);
    }

    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Concatenates the passed comments in a position-preserving way. (see also
     * JMLTransformer::concatenate(), which does the same thing for Recoder ASTs)
     */
    private String concatenate(Comment[] comments) {
        if (comments.length == 0) {
            return "";
        }
        StringBuilder sb = new StringBuilder(comments[0].getText());

        for (int i = 1; i < comments.length; i++) {
            var relativePos = comments[i].getRelativePosition();
            for (int j = 0; j < relativePos.getLine(); j++) {
                sb.append("\n");
            }
            for (int j = 0; j < relativePos.getColumn(); j++) {
                sb.append(" ");
            }
            sb.append(comments[i].getText());
        }

        return sb.toString();
    }

    private int getIndexOfMethodDecl(IProgramMethod pm, TextualJMLConstruct[] constructsArray) {
        for (int i = 0; i < constructsArray.length; i++) {
            if (constructsArray[i] instanceof TextualJMLMethodDecl) {
                TextualJMLMethodDecl methodDecl = (TextualJMLMethodDecl) constructsArray[i];
                if (methodDecl.getMethodName().equals(pm.getName())) {
                    return i;
                }
            }
        }
        return -1;
    }

    // includes unchecked exceptions (instances of Error or RuntimeException)
    // (see resolution to issue #1379)
    private ParserRuleContext getDefaultSignalsOnly(IProgramMethod pm) {
        if (pm.getThrown() == null) {
            return JmlFacade.parseClause(DEFAULT_SIGNALS_ONLY);
        }

        ImmutableArray<TypeReference> exceptions = pm.getThrown().getExceptions();

        if (exceptions == null) {
            return JmlFacade.parseClause(DEFAULT_SIGNALS_ONLY);
        }

        StringBuilder b = new StringBuilder();
        b.append(ERROR).append(", ").append(RUNTIME_EXCEPTION);

        for (int i = 0; i < exceptions.size(); i++) {
            if (services.getJavaInfo().isSubtype(exceptions.get(i).getKeYJavaType(),
                services.getJavaInfo().getKeYJavaType(THROWABLE))) {
                b.append(", ").append(exceptions.get(i).getKeYJavaType().getFullName());
            }
        }

        if (b.length() == 0) {
            b.append("\\nothing");
        }
        return JmlFacade.parseClause("signals_only " + b + ";");
    }

    /**
     * creates a JML specification expressing that the given variable/field is not null and in case
     * of a reference array type that also its elements are non-null In case of implicit fields or
     * primitive typed fields/variables the empty set is returned
     *
     * @param varName the String specifying the variable/field name
     * @param kjt the KeYJavaType representing the variables/field declared type
     * @param isImplicitVar a boolean indicating if the field is an implicit one (in which case
     *        no
     * @param services the services object
     * @return set of formulas specifying non-nullity for field/variables
     */
    public static ImmutableSet<LabeledParserRuleContext> createNonNullPositionedString(
            String varName, KeYJavaType kjt, boolean isImplicitVar, Location location,
            Services services) {
        ImmutableSet<LabeledParserRuleContext> result = DefaultImmutableSet.nil();
        final Type varType = kjt.getJavaType();

        final TypeConverter typeConverter = services.getTypeConverter();
        if (typeConverter.isReferenceType(varType) && !isImplicitVar) {
            final int arrayDepth = arrayDepth(varType, services);

            // use special "deep" non null predicate (see bug #1392)
            // ... looks a bit like a hack with those DL escapes ...
            final String nonNullString =
                arrayDepth > 0 ? format("\\dl_nonNull(\\dl_heap(),%s,%d)", varName, arrayDepth)
                        : format("%s != null", varName);
            final ParserRuleContext ps =
                JmlFacade.parseExpr(new PositionedString(nonNullString, location));
            result = result.add(new LabeledParserRuleContext(ps, IMPL_TERM_LABEL));
        }
        return result;
    }


    /**
     * Get the depth for the nonNull predicate. The depth is 0 for non array types, its dimension
     * for reference array types, and its dimension -1 for array types with primitive base type.
     */
    public static int arrayDepth(Type type, Services services) {
        assert services != null;
        final TypeConverter tc = services.getTypeConverter();
        if (type instanceof ArrayType) {
            final int d = ((ArrayType) type).getDimension();
            while (type instanceof ArrayType) {
                type = ((ArrayType) type).getBaseType().getKeYJavaType().getJavaType();
            }
            return tc.isReferenceType(type) ? d : d - 1;
        } else {
            return 0;
        }
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public ImmutableSet<SpecificationElement> extractClassSpecs(KeYJavaType kjt)
            throws SLTranslationException {
        ImmutableSet<SpecificationElement> result = DefaultImmutableSet.nil();

        // primitive types have no class invariants
        if (!(kjt.getJavaType() instanceof TypeDeclaration)) {
            return result;
        }

        // get type declaration, file name
        TypeDeclaration td = (TypeDeclaration) kjt.getJavaType();
        URI fileName = td.getPositionInfo().getURI().orElse(null);

        // add invariants for non_null fields
        for (MemberDeclaration member : td.getMembers()) {
            if (member instanceof FieldDeclaration) {
                VisibilityModifier visibility = null;
                for (Modifier mod : member.getModifiers()) {
                    if (mod instanceof VisibilityModifier) {
                        visibility = (VisibilityModifier) mod;
                        break;
                    }
                }
                // check for spec_* modifiers (bug #1280)
                if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member, "spec_public")) {
                    visibility = new Public();
                } else if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member,
                    "spec_protected")) {
                    visibility = new Protected();
                }

                for (FieldSpecification field : ((FieldDeclaration) member)
                        .getFieldSpecifications()) {
                    // add a static invariant for static fields
                    boolean isStatic = member.isStatic();

                    // add invariant only for fields of reference types
                    // and not for implicit fields.
                    if (!JMLInfoExtractor.isNullable(field.getProgramName(), td)) {
                        ImmutableSet<LabeledParserRuleContext> nonNullInvs =
                            createNonNullPositionedString(field.getProgramName(),
                                field.getProgramVariable().getKeYJavaType(),
                                field instanceof ImplicitFieldSpecification,
                                new Location(fileName, member.getEndPosition()), services);
                        for (LabeledParserRuleContext classInv : nonNullInvs) {
                            final ClassInvariant jmlClassInvariant =
                                jsf.createJMLClassInvariant(kjt, visibility, isStatic, classInv);
                            result = result.add(jmlClassInvariant);
                        }
                    }
                }
            }
        }

        // iterate over all children
        for (int i = 0, n = td.getChildCount(); i <= n; i++) {
            // collect comments
            // (last position are comments of type declaration itself)
            Comment[] comments = null;
            if (i < n) {
                ProgramElement child = td.getChildAt(i);
                comments = child.getComments();
                // skip model and ghost elements
                // (their comments are duplicates of other comments)
                if ((child instanceof FieldDeclaration && (((FieldDeclaration) child).isGhost()
                        || ((FieldDeclaration) child).isModel()))
                        || (child instanceof IProgramMethod
                                && ((IProgramMethod) child).isModel())) {
                    continue;
                }
            } else if (td.getComments() != null) {
                comments = td.getComments();
            }
            if (comments == null || comments.length == 0) {
                continue;
            }

            // concatenate comments, determine position
            String concatenatedComment = concatenate(comments);
            Position pos = comments[0].getStartPosition();

            // call preparser
            var parser = new PreParser();
            ImmutableList<TextualJMLConstruct> constructs =
                parser.parseClassLevel(concatenatedComment, fileName, pos);
            warnings = warnings.append(parser.getWarnings());

            // create class invs out of textual constructs, add them to result
            for (TextualJMLConstruct c : constructs) {
                try {
                    if (c instanceof TextualJMLClassInv) {
                        TextualJMLClassInv textualInv = (TextualJMLClassInv) c;
                        ClassInvariant inv = jsf.createJMLClassInvariant(kjt, textualInv);
                        result = result.add(inv);
                    } else if (c instanceof TextualJMLInitially) {
                        TextualJMLInitially textualRep = (TextualJMLInitially) c;
                        InitiallyClause inc = jsf.createJMLInitiallyClause(kjt, textualRep);
                        result = result.add(inc);
                    } else if (c instanceof TextualJMLRepresents) {
                        TextualJMLRepresents textualRep = (TextualJMLRepresents) c;
                        ClassAxiom rep = jsf.createJMLRepresents(kjt, textualRep);
                        result = result.add(rep);
                    } else if (c instanceof TextualJMLDepends) {
                        TextualJMLDepends textualDep = (TextualJMLDepends) c;
                        Contract depContract = jsf.createJMLDependencyContract(kjt, textualDep);
                        result = result.add(depContract);
                    } else if (c instanceof TextualJMLClassAxiom) {
                        ClassAxiom ax = jsf.createJMLClassAxiom(kjt, (TextualJMLClassAxiom) c);
                        result = result.add(ax);
                    } else {
                        // DO NOTHING
                        // There may be other kinds of JML constructs which are
                        // not specifications.
                    }
                } catch (SLWarningException e) {
                    warnings = warnings.append(e.getWarning());
                }
            }
        }

        return result;
    }

    @Override
    public ImmutableSet<SpecificationElement> extractMethodSpecs(IProgramMethod pm)
            throws SLTranslationException {
        return extractMethodSpecs(pm, true);
    }

    /**
     * Extracts method specifications (i.e., contracts) from Java+JML input.
     *
     * @param pm method to extract for
     * @param addInvariant whether to add <i>static</i> invariants to pre- and post-conditions
     */
    @Override
    public ImmutableSet<SpecificationElement> extractMethodSpecs(IProgramMethod pm,
            boolean addInvariant) throws SLTranslationException {
        ImmutableSet<SpecificationElement> result = DefaultImmutableSet.nil();

        // get type declaration, file name
        TypeDeclaration td = (TypeDeclaration) pm.getContainerType().getJavaType();
        URI fileName = td.getPositionInfo().getURI().orElse(null);

        // determine purity
        final boolean isStrictlyPure = JMLInfoExtractor.isStrictlyPure(pm);
        final boolean isPure = JMLInfoExtractor.isPure(pm);
        final boolean isHelper = JMLInfoExtractor.isHelper(pm);

        // get textual JML constructs
        Comment[] comments = pm.getComments();
        ImmutableList<TextualJMLConstruct> constructs;
        if (comments.length != 0) {
            // concatenate comments, determine position
            String concatenatedComment = concatenate(comments);
            Position pos = comments[0].getStartPosition();

            // call preparser
            PreParser parser = new PreParser();
            constructs = parser.parseClassLevel(concatenatedComment, fileName, pos);
            warnings = warnings.append(parser.getWarnings());
        } else {
            constructs = ImmutableSLList.nil();
        }

        // create JML contracts out of constructs, add them to result
        TextualJMLConstruct[] constructsArray =
            constructs.toArray(new TextualJMLConstruct[constructs.size()]);

        int startPos;
        TextualJMLMethodDecl modelMethodDecl = null;
        if (pm.isModel()) {
            startPos = getIndexOfMethodDecl(pm, constructsArray) - 1;
            modelMethodDecl = (TextualJMLMethodDecl) constructsArray[startPos + 1];
            if (startPos < 0 || !(constructsArray[startPos] instanceof TextualJMLSpecCase)) {
                // Special case, the method is model, but does not have any
                // specification
                // create an empty one and insert it:
                TextualJMLSpecCase modelSpec =
                    new TextualJMLSpecCase(ImmutableSLList.nil(), Behavior.NORMAL_BEHAVIOR);
                TextualJMLConstruct[] t = new TextualJMLConstruct[constructsArray.length + 1];
                startPos++;
                System.arraycopy(constructsArray, 0, t, 0, startPos);
                System.arraycopy(constructsArray, startPos, t, startPos + 1,
                    constructsArray.length - startPos);
                t[startPos] = modelSpec;
                constructsArray = t;
            }
            assert startPos != constructsArray.length - 1;
        } else {
            startPos = constructsArray.length - 1;
        }
        for (int i = startPos; i >= 0 && constructsArray[i] instanceof TextualJMLSpecCase; i--) {
            TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructsArray[i];
            if (modelMethodDecl != null && modelMethodDecl.getMethodDefinition() != null) {
                specCase.addClause(AXIOMS, null, modelMethodDecl.getMethodDefinition());
            }
            // add purity. Strict purity overrides purity.
            if (isStrictlyPure || pm.isModel()) {
                for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
                    specCase.addClause(ASSIGNABLE, heap.name(),
                        JmlFacade.parseExpr("\\strictly_nothing"));
                }
            } else if (isPure) {
                for (LocationVariable heap : HeapContext.getModHeaps(services, false)) {
                    specCase.addClause(ASSIGNABLE, heap.name(), JmlFacade.parseExpr("\\nothing"));
                }
            }

            // add invariants
            if (!isHelper && pm.getStateCount() > 0 && (!pm.isStatic() || addInvariant)) {
                // for a static method translate \inv once again, otherwise use
                // the internal symbol
                final String invString = pm.isStatic() ? "\\inv" : "<inv>";
                final String invFreeString = pm.isStatic() ? "\\inv_free" : "<inv_free>";

                KeYJavaType classType = pm.getContainerType();
                boolean hasFreeInvariant = services.getSpecificationRepository()
                        .getClassInvariants(classType).stream().anyMatch(ClassInvariant::isFree);

                if (!pm.isConstructor()) {
                    specCase.addClause(REQUIRES, new LabeledParserRuleContext(
                        JmlFacade.parseExpr(invString), IMPL_TERM_LABEL));
                    if (hasFreeInvariant) {
                        specCase.addClause(REQUIRES_FREE, new LabeledParserRuleContext(
                            JmlFacade.parseExpr(invFreeString), IMPL_TERM_LABEL));
                    }
                } else if (addInvariant) {
                    // add static invariant to constructor's precondition
                    specCase.addClause(REQUIRES, new LabeledParserRuleContext(
                        JmlFacade.parseExpr(format("%s.\\inv", pm.getName())),
                        IMPL_TERM_LABEL));
                    if (hasFreeInvariant) {
                        specCase.addClause(REQUIRES_FREE, new LabeledParserRuleContext(
                            JmlFacade.parseExpr(format("%s.\\inv_free", pm.getName())),
                            IMPL_TERM_LABEL));
                    }
                }
                if (specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                    specCase.addClause(ENSURES, new LabeledParserRuleContext(
                        JmlFacade.parseExpr(invString), IMPL_TERM_LABEL));
                    if (hasFreeInvariant) {
                        specCase.addClause(ENSURES_FREE, new LabeledParserRuleContext(
                            JmlFacade.parseExpr(invFreeString), IMPL_TERM_LABEL));
                    }

                }
                if (specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR && !pm.isModel()) {
                    specCase.addClause(TextualJMLSpecCase.Clause.SIGNALS,
                        new LabeledParserRuleContext(
                            JmlFacade.parseClause(format("signals (Throwable e) %s;", invString)),
                            IMPL_TERM_LABEL));

                }
            }

            // add non-null preconditions
            for (int j = 0, n = pm.getParameterDeclarationCount(); j < n; j++) {
                final VariableSpecification paramDecl =
                    pm.getParameterDeclarationAt(j).getVariableSpecification();
                if (!JMLInfoExtractor.parameterIsNullable(pm, j)) {
                    // no additional precondition for primitive types!
                    // createNonNullPos... takes care of that
                    final ImmutableSet<LabeledParserRuleContext> nonNullParams =
                        createNonNullPositionedString(paramDecl.getName(),
                            paramDecl.getProgramVariable().getKeYJavaType(), false,
                            new Location(fileName,
                                pm.getStartPosition()),
                            services);
                    for (LabeledParserRuleContext nonNull : nonNullParams) {
                        specCase.addClause(REQUIRES, nonNull);
                    }
                }
            }

            // add non-null postcondition
            KeYJavaType resultType = pm.getReturnType();

            if (!pm.isVoid() && !pm.isConstructor() && !JMLInfoExtractor.resultIsNullable(pm)
                    && specCase.getBehavior() != Behavior.EXCEPTIONAL_BEHAVIOR) {
                final ImmutableSet<LabeledParserRuleContext> resultNonNull =
                    createNonNullPositionedString("\\result", resultType, false,
                        new Location(fileName,
                            pm.getStartPosition()),
                        services);
                for (LabeledParserRuleContext nonNull : resultNonNull) {
                    specCase.addClause(ENSURES, nonNull);
                }
            }

            // add implicit signals-only if omitted
            if (specCase.getSignalsOnly().isEmpty()
                    && specCase.getBehavior() != Behavior.NORMAL_BEHAVIOR && !pm.isModel()) {
                specCase.addClause(SIGNALS_ONLY, getDefaultSignalsOnly(pm));
            }

            // translate contract
            try {
                ImmutableSet<Contract> contracts = jsf.createJMLOperationContracts(pm, specCase);
                for (Contract contract : contracts) {
                    result = result.add(contract);
                }
            } catch (SLWarningException e) {
                warnings = warnings.append(e.getWarning());
            }
        }

        return result;
    }

    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method,
            final StatementBlock block) throws SLTranslationException {
        return createBlockContracts(method, new LinkedList<>(), block, block.getComments());
    }

    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method,
            final LabeledStatement labeled) throws SLTranslationException {
        final List<Label> labels = new LinkedList<>();
        labels.add(labeled.getLabel());
        Statement nextNonLabeled = labeled.getBody();
        while (nextNonLabeled instanceof LabeledStatement) {
            final LabeledStatement currentLabeled = (LabeledStatement) nextNonLabeled;
            labels.add(currentLabeled.getLabel());
            nextNonLabeled = currentLabeled.getBody();
        }
        if (nextNonLabeled instanceof StatementBlock) {
            return createBlockContracts(method, labels, (StatementBlock) nextNonLabeled,
                labeled.getComments());
        } else {
            return DefaultImmutableSet.nil();
        }
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final LoopStatement loop) throws SLTranslationException {
        return createLoopContracts(method, new LinkedList<>(), loop, loop.getComments());
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final StatementBlock block) throws SLTranslationException {
        return createLoopContracts(method, new LinkedList<>(), block, block.getComments());
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final LabeledStatement labeled) throws SLTranslationException {
        final List<Label> labels = new LinkedList<>();
        labels.add(labeled.getLabel());
        Statement nextNonLabeled = labeled.getBody();
        while (nextNonLabeled instanceof LabeledStatement) {
            final LabeledStatement currentLabeled = (LabeledStatement) nextNonLabeled;
            labels.add(currentLabeled.getLabel());
            nextNonLabeled = currentLabeled.getBody();
        }
        if (nextNonLabeled instanceof StatementBlock) {
            return createLoopContracts(method, labels, (StatementBlock) nextNonLabeled,
                labeled.getComments());
        } else if (nextNonLabeled instanceof LoopStatement) {
            return createLoopContracts(method, labels, (LoopStatement) nextNonLabeled,
                labeled.getComments());
        } else {
            return DefaultImmutableSet.nil();
        }
    }

    @Override
    public ImmutableSet<MergeContract> extractMergeContracts(IProgramMethod method,
            MergePointStatement mps, ImmutableList<ProgramVariable> methodParams)
            throws SLTranslationException {
        // In cases of specifications immediately following each other (like a
        // merge_point and a block contract / loop invariant), it might happen
        // that we're passed multiple constructs here. Therefore, we filter the
        // merge point specific parts here
        final TextualJMLConstruct[] constructs =
            Arrays.stream(parseMethodLevelComments(mps.getComments(), getFileName(method)))
                    .filter(c -> c instanceof TextualJMLMergePointDecl)
                    .toArray(TextualJMLConstruct[]::new);

        return jsf.createJMLMergeContracts(method, mps, (TextualJMLMergePointDecl) constructs[0]);
    }

    private ImmutableSet<BlockContract> createBlockContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block, final Comment[] comments)
            throws SLTranslationException {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        // For some odd reason every comment block appears twice; thus we remove
        // duplicates.
        final TextualJMLConstruct[] constructs =
            parseMethodLevelComments(removeDuplicates(comments), getFileName(method));
        for (int i = constructs.length - 1; i >= 0
                && constructs[i] instanceof TextualJMLSpecCase; i--) {
            final TextualJMLSpecCase specificationCase = (TextualJMLSpecCase) constructs[i];
            try {
                result = result.union(
                    jsf.createJMLBlockContracts(method, labels, block, specificationCase));
            } catch (final SLWarningException exception) {
                warnings = warnings.append(exception.getWarning());
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final LoopStatement loop, final Comment[] comments)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        // For some odd reason every comment block appears twice; thus we remove
        // duplicates.
        final TextualJMLConstruct[] constructs =
            parseMethodLevelComments(removeDuplicates(comments), getFileName(method));
        for (int i = constructs.length - 1; i >= 0
                && constructs[i] instanceof TextualJMLSpecCase; i--) {
            final TextualJMLSpecCase specificationCase = (TextualJMLSpecCase) constructs[i];
            try {
                result = result
                        .union(jsf.createJMLLoopContracts(method, labels, loop, specificationCase));
            } catch (final SLWarningException exception) {
                warnings = warnings.append(exception.getWarning());
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block, final Comment[] comments)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        // For some odd reason every comment block appears twice; thus we remove
        // duplicates.
        final TextualJMLConstruct[] constructs =
            parseMethodLevelComments(removeDuplicates(comments), getFileName(method));
        for (int i = constructs.length - 1; i >= 0
                && constructs[i] instanceof TextualJMLSpecCase; i--) {
            final TextualJMLSpecCase specificationCase = (TextualJMLSpecCase) constructs[i];
            try {
                result = result.union(
                    jsf.createJMLLoopContracts(method, labels, block, specificationCase));
            } catch (final SLWarningException exception) {
                warnings = warnings.append(exception.getWarning());
            }
        }
        return result;
    }

    private URI getFileName(final IProgramMethod method) {
        final TypeDeclaration type = (TypeDeclaration) method.getContainerType().getJavaType();
        return type.getPositionInfo().getURI().orElse(null);
    }

    private TextualJMLConstruct[] parseMethodLevelComments(final Comment[] comments,
            final URI fileName) {
        if (comments.length == 0) {
            return new TextualJMLConstruct[0];
        }
        final String concatenatedComment = concatenate(comments);
        final Position position = comments[0].getStartPosition();
        final var parser = new PreParser();
        final ImmutableList<TextualJMLConstruct> constructs =
            parser.parseMethodLevel(concatenatedComment, fileName, position);
        warnings = warnings.append(parser.getWarnings());
        return constructs.toArray(new TextualJMLConstruct[constructs.size()]);
    }

    private Comment[] removeDuplicates(final Comment[] comments) {
        final Set<Comment> uniqueComments = new LinkedHashSet<>(Arrays.asList(comments));
        return uniqueComments.toArray(new Comment[0]);
    }

    @Override
    public LoopSpecification extractLoopInvariant(IProgramMethod pm, LoopStatement loop) {
        LoopSpecification result = null;

        // get type declaration, file name
        TypeDeclaration td = (TypeDeclaration) pm.getContainerType().getJavaType();
        URI fileName = td.getPositionInfo().getURI().orElse(null);

        // get comments
        Comment[] comments = loop.getComments();
        if (comments.length == 0) {
            return result;
        }

        // concatenate comments, determine position
        String concatenatedComment = concatenate(comments);
        Position pos = comments[0].getStartPosition();

        // call preparser
        var parser = new PreParser();
        ImmutableList<TextualJMLConstruct> constructs =
            parser.parseMethodLevel(concatenatedComment, fileName, pos);
        warnings = warnings.append(parser.getWarnings());

        // create JML loop invariant out of last construct
        if (constructs.size() == 0) {
            return result;
        }
        TextualJMLConstruct c = constructs.take(constructs.size() - 1).head();
        if (c instanceof TextualJMLLoopSpec) {
            TextualJMLLoopSpec textualLoopSpec = (TextualJMLLoopSpec) c;
            result = jsf.createJMLLoopInvariant(pm, loop, textualLoopSpec);

            // Check that a decreases clause exists
            if (result.getInternalVariant() == null) {
                PositionInfo info = loop.getPositionInfo();
                warnings = warnings.append(
                    new PositionedString(
                        "Missing \"decreases\" for loop invariant. " +
                            "Termination of this loop will not be provable.",
                        new Location(info.getURI().orElse(null), info.getStartPosition())));
            }
        }
        return result;
    }

    @Override
    public ImmutableList<PositionedString> getWarnings() {
        return warnings.append(JMLTransformer.getWarningsOfLastInstance());
    }
}
