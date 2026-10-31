/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml;

import java.net.URI;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.KeYJPMapping;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.ArrayType;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.java.ast.statement.LabeledStatement;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.ast.statement.MergePointStatement;
import de.uka.ilkd.key.java.transformations.MarkerStatementHelper;
import de.uka.ilkd.key.ldt.FinalHeapResolution;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.jml.translation.JmlToTextual;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLWarningException;

import org.key_project.util.collection.*;
import org.key_project.util.parsing.Location;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.jml.body.JmlClassAccessibleDeclaration;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.body.JmlMethodDeclaration;
import com.github.javaparser.ast.jml.body.JmlRepresentsDeclaration;
import com.github.javaparser.ast.jml.clauses.ContractType;
import com.github.javaparser.ast.jml.clauses.JmlContract;
import com.github.javaparser.ast.jml.doc.JmlDocStmt;
import com.github.javaparser.ast.key.KeyMergePointStmt;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.Nullable;

import static java.lang.String.format;

/**
 * Extracts JML class invariants and operation contracts from the JMLtk AST. The JMLtk AST is the
 * single source of truth for the specifications: contracts are attached to the corresponding
 * nodes ({@link NodeWithContracts}) and class level specifications are members of the JMLtk type.
 * The KeY elements are resolved back to their JMLtk counterparts via
 * {@link de.uka.ilkd.key.java.KeYJPMapping#nodeFromKeY}. This is the public interface to the jml
 * package.
 * <p>
 * The actual translation into KeY specifications is delegated to the {@link JMLSpecFactory}; this
 * class only distributes the JML constructs to the right factory methods.
 */
public final class JMLSpecExtractor implements SpecExtractor {

    private final Services services;
    private final JMLSpecFactory jsf;
    private ImmutableList<PositionedString> warnings = ImmutableList.nil();

    /**
     * This is the term label for implicit specification clauses. This is important for
     * well-definedness checks. Hence, do not change its usages unless you understand and have
     * thought about the semantics of the corresponding well-definedness checks.
     **/
    private static final TermLabel IMPL_TERM_LABEL =
        ParameterlessTermLabel.IMPLICIT_SPECIFICATION_LABEL;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public JMLSpecExtractor(InitConfig initConfig) {
        FinalHeapResolution.rememberIfFinalEnabled(initConfig);
        this.services = initConfig.getServices();
        this.jsf = new JMLSpecFactory(services);
    }

    private KeYJPMapping mapping() {
        return services.getJavaInfo().rec2key();
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
            final var ps = JmlFacade.parseExpr(new PositionedString(nonNullString, location));
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
        if (!(kjt.getJavaType() instanceof TypeDeclaration td)) {
            return result;
        }

        // get type declaration, file name
        URI fileName = td.getPositionInfo().getURI().orElse(null);

        // add invariants for non_null fields
        for (MemberDeclaration member : td.getMembers()) {
            if (member instanceof FieldDeclaration) {
                ModifierKind visibility = null;
                for (Modifier mod : member.getModifiers()) {
                    final ModifierKind modKind = mod.getKind();
                    if (modKind.isVisibility()) {
                        visibility = modKind;
                        break;
                    }
                }
                // check for spec_* modifiers (bug #1280)
                if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member,
                    ModifierKind.JML_SPEC_PUBLIC)) {
                    visibility = ModifierKind.PUBLIC;
                } else if (JMLInfoExtractor.hasJMLModifier((FieldDeclaration) member,
                    ModifierKind.JML_SPEC_PROTECTED)) {
                    visibility = ModifierKind.PROTECTED;
                }

                for (FieldSpecification field : ((FieldDeclaration) member)
                        .getFieldSpecifications()) {
                    // add a static invariant for static fields
                    boolean isStatic = member.isStatic();

                    // add invariant only for fields of reference types
                    // and not for implicit fields.
                    if (!JMLInfoExtractor.isNullable((FieldDeclaration) member, td)) {
                        ImmutableSet<LabeledParserRuleContext> nonNullInvs =
                            createNonNullPositionedString(field.getProgramName(),
                                field.getProgramVariable().getKeYJavaType(),
                                field.isImplicit(),
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

        // create class specifications out of the JML class level declarations in the JMLtk type
        // and add them to result. The JMLtk type is the single source of truth: invariants,
        // initially clauses, axioms, represents clauses and accessible-clauses are members of it,
        // and it is resolved through the KeY-JMLtk mapping.
        if (mapping().nodeFromKeY(
            td) instanceof com.github.javaparser.ast.body.TypeDeclaration<?> jmlType) {
            for (BodyDeclaration<?> member : jmlType.getMembers()) {
                try {
                    if (member instanceof JmlClassExprDeclaration decl) {
                        switch (decl.getKind()) {
                            case INVARIANT, INVARIANT_FREE -> result =
                                result.add(jsf.createJMLClassInvariant(kjt, decl));
                            case INITIALLY -> result =
                                result.add(jsf.createJMLInitiallyClause(kjt, decl));
                            case AXIOM -> result =
                                result.add(jsf.createJMLClassAxiom(kjt, decl));
                            default -> {
                                // DO NOTHING (there may be other class level constructs which are
                                // not specifications, e.g. invariants_redundantly)
                            }
                        }
                    } else if (member instanceof JmlRepresentsDeclaration rep) {
                        result = result.add(jsf.createJMLRepresents(kjt, rep));
                    } else if (member instanceof JmlClassAccessibleDeclaration acc) {
                        result = result.add(jsf.createJMLDependencyContract(kjt, acc));
                    }
                    // DO NOTHING for other JML constructs (JmlMethodDeclaration,
                    // JmlFieldDeclaration) and regular Java members, which are not class level
                    // specifications themselves.
                } catch (SLWarningException e) {
                    warnings = warnings.append(e.getWarning());
                }
            }
        }
        return result;
    }

    @Override
    public List<SpecificationElement> extractMethodSpecs(IProgramMethod pm)
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
    public List<SpecificationElement> extractMethodSpecs(IProgramMethod pm, boolean addInvariant)
            throws SLTranslationException {
        List<SpecificationElement> result = new ArrayList<>();

        // Resolve the JMLtk carrier of the specification: a model method is wrapped in a
        // JmlMethodDeclaration (carrying the optional contract and the method definition), a
        // regular method/constructor is itself a NodeWithContracts.
        Node node = mapping().nodeFromKeY(pm.getMethodDeclaration());
        if (node instanceof JmlMethodDeclaration wrapper) {
            // Model method: the method definition is a specification (a source of an AXIOMS
            // clause), so it is re-serialized for the translation.
            ParserRuleContext modelMethodDefinition = null;
            if (wrapper.getMethodDeclaration()
                    .hasModifier(com.github.javaparser.ast.Modifier.DefaultKeyword.JML_MODEL)) {
                modelMethodDefinition = JmlToTextual.toMethodDecl(wrapper).getMethodDefinition();
            }
            if (wrapper.getContract().isPresent()) {
                addOperationContracts(result, pm, wrapper.getContract().get(),
                    modelMethodDefinition, addInvariant);
            } else if (modelMethodDefinition != null) {
                // model method without an explicit contract: the method definition itself serves
                // as the specification
                try {
                    for (Contract contract : jsf.createJMLModelMethodContracts(pm,
                        modelMethodDefinition, addInvariant)) {
                        result.add(contract);
                    }
                } catch (SLWarningException e) {
                    warnings = warnings.append(e.getWarning());
                }
            }
        } else if (node instanceof NodeWithContracts<?> carrier) {
            for (JmlContract contract : carrier.getContracts()) {
                addOperationContracts(result, pm, contract, null, addInvariant);
            }
        }
        return result;
    }

    /**
     * Translates a single JML contract into operation contracts for the given method and adds
     * them to the result list.
     *
     * @param modelMethodDefinition the textual definition of a model method used as an AXIOMS
     *        clause, or {@code null} for regular methods
     */
    private void addOperationContracts(List<SpecificationElement> result, IProgramMethod pm,
            JmlContract contract, @Nullable ParserRuleContext modelMethodDefinition,
            boolean addInvariant) throws SLTranslationException {
        try {
            ImmutableSet<Contract> contracts = jsf.createJMLOperationContracts(pm, contract,
                modelMethodDefinition, addInvariant);
            for (Contract c : contracts) {
                result.add(c);
            }
        } catch (SLWarningException e) {
            warnings = warnings.append(e.getWarning());
        }
    }

    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method,
            final StatementBlock block) throws SLTranslationException {
        return createBlockContracts(method, new LinkedList<>(), block);
    }

    @Override
    public ImmutableSet<BlockContract> extractBlockContracts(final IProgramMethod method,
            final LabeledStatement labeled) throws SLTranslationException {
        final List<Label> labels = new LinkedList<>();
        labels.add(labeled.getLabel());
        Statement nextNonLabeled = labeled.getBody();
        while (nextNonLabeled instanceof LabeledStatement currentLabeled) {
            labels.add(currentLabeled.getLabel());
            nextNonLabeled = currentLabeled.getBody();
        }
        if (nextNonLabeled instanceof StatementBlock) {
            return createBlockContracts(method, labels, (StatementBlock) nextNonLabeled);
        } else {
            return DefaultImmutableSet.nil();
        }
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final LoopStatement loop) throws SLTranslationException {
        return createLoopContracts(method, new LinkedList<>(), loop);
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final StatementBlock block) throws SLTranslationException {
        return createLoopContracts(method, new LinkedList<>(), block);
    }

    @Override
    public ImmutableSet<LoopContract> extractLoopContracts(final IProgramMethod method,
            final LabeledStatement labeled) throws SLTranslationException {
        final List<Label> labels = new LinkedList<>();
        labels.add(labeled.getLabel());
        Statement nextNonLabeled = labeled.getBody();
        while (nextNonLabeled instanceof LabeledStatement currentLabeled) {
            labels.add(currentLabeled.getLabel());
            nextNonLabeled = currentLabeled.getBody();
        }
        if (nextNonLabeled instanceof StatementBlock) {
            return createLoopContracts(method, labels, (StatementBlock) nextNonLabeled);
        } else if (nextNonLabeled instanceof LoopStatement) {
            return createLoopContracts(method, labels, (LoopStatement) nextNonLabeled);
        } else {
            return DefaultImmutableSet.nil();
        }
    }

    @Override
    public ImmutableSet<MergeContract> extractMergeContracts(IProgramMethod method,
            MergePointStatement mps, ImmutableList<LocationVariable> methodParams)
            throws SLTranslationException {
        // Resolve the JMLtk KeyMergePointStmt through the mapping: it carries the merge point
        // expression from which the textual merge contract is re-derived. For merge points that
        // JMLtk left unparsed, the JMLTransformer fallback re-parsed the comment with KeY's own
        // JML grammar and attached the parse tree to the leftover JmlDocStmt.
        Node jmlNode = mapping().nodeFromKeY(mps);
        if (jmlNode instanceof KeyMergePointStmt kms) {
            return jsf.createJMLMergeContracts(method, mps, kms);
        } else if (jmlNode instanceof JmlDocStmt jds
                && jds.containsData(MarkerStatementHelper.KEY_JML_FALLBACK)) {
            if (jds.getData(
                MarkerStatementHelper.KEY_JML_FALLBACK) instanceof JmlParser.Merge_point_statementContext ctx) {
                return jsf.createJMLMergeContracts(method, mps, ctx);
            }
            return DefaultImmutableSet.nil();
        }
        return ImmutableSet.empty();
    }

    private ImmutableSet<BlockContract> createBlockContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block)
            throws SLTranslationException {
        ImmutableSet<BlockContract> result = DefaultImmutableSet.nil();
        if (mapping().nodeFromKeY(block) instanceof NodeWithContracts<?> carrier) {
            for (JmlContract contract : carrier.getContracts()) {
                // loop contracts and loop invariants are no block contracts
                if (contract.getType() != ContractType.LOOP
                        && contract.getType() != ContractType.LOOP_INV) {
                    try {
                        result = result.union(jsf.createJMLBlockContracts(method, labels, block,
                            contract));
                    } catch (final SLWarningException exception) {
                        warnings = warnings.append(exception.getWarning());
                    }
                }
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final LoopStatement loop)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        if (mapping().nodeFromKeY(loop) instanceof NodeWithContracts<?> carrier) {
            for (JmlContract contract : carrier.getContracts()) {
                if (contract.getType() == ContractType.LOOP) {
                    try {
                        result = result.union(jsf.createJMLLoopContracts(method, labels, loop,
                            contract));
                    } catch (final SLWarningException exception) {
                        warnings = warnings.append(exception.getWarning());
                    }
                }
            }
        }
        return result;
    }

    private ImmutableSet<LoopContract> createLoopContracts(final IProgramMethod method,
            final List<Label> labels, final StatementBlock block)
            throws SLTranslationException {
        ImmutableSet<LoopContract> result = DefaultImmutableSet.nil();
        if (mapping().nodeFromKeY(block) instanceof NodeWithContracts<?> carrier) {
            for (JmlContract contract : carrier.getContracts()) {
                if (contract.getType() == ContractType.LOOP) {
                    try {
                        result = result.union(jsf.createJMLLoopContracts(method, labels, block,
                            contract));
                    } catch (final SLWarningException exception) {
                        warnings = warnings.append(exception.getWarning());
                    }
                }
            }
        }
        return result;
    }

    @Override
    public LoopSpecification extractLoopInvariant(IProgramMethod pm, LoopStatement loop) {
        LoopSpecification result = null;

        if (mapping().nodeFromKeY(loop) instanceof NodeWithContracts<?> carrier) {
            // create JML loop invariant out of the last loop invariant contract
            for (int i = carrier.getContracts().size() - 1; i >= 0; i--) {
                JmlContract c = carrier.getContracts().get(i);
                if (c.getType() == ContractType.LOOP_INV) {
                    result = jsf.createJMLLoopInvariant(pm, loop, c);

                    // Check that a decreases clause exists
                    if (result.getInternalVariant() == null) {
                        PositionInfo info = loop.getPositionInfo();
                        warnings = warnings.append(
                            new PositionedString(
                                "Missing \"decreases\" for loop invariant. " +
                                    "Termination of this loop will not be provable.",
                                new Location(info.getURI().orElse(null), info.getStartPosition())));
                    }
                    break;
                }
            }
        }
        return result;
    }

    @Override
    public ImmutableList<PositionedString> getWarnings() {
        return warnings;
    }

    @Override
    public Contract createDefaultContract(IProgramMethod method, boolean useSoundDefault) {
        return jsf.createDefaultContract(method, useSoundDefault);
    }
}
