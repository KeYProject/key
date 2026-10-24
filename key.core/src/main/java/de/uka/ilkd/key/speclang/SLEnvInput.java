/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaService;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import de.uka.ilkd.key.java.ast.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.ast.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.ast.statement.*;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.java.visitor.JavaASTWalker;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractEnvInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ContractRegistry;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * EnvInput for standalone specification language front ends.
 */
public final class SLEnvInput extends AbstractEnvInput {
    private static final Logger LOGGER = LoggerFactory.getLogger(SLEnvInput.class);


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public SLEnvInput(@Nullable Path javaPath, List<Path> classPath, @Nullable Path bootClassPath,
            Profile profile, List<Path> includes) {
        super(getLanguage() + " specifications", javaPath, classPath, bootClassPath, profile,
            includes);
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    public static String getLanguage() {
        GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        if (gs.isUseJML()) {
            return "JML";
        } else {
            return "no";
        }
    }

    private KeYJavaType[] sortKJTs(KeYJavaType[] kjts) {
        Arrays.sort(kjts, (o1, o2) -> {
            assert o1.getFullName() != null : "type without name: " + o1;
            assert o2.getFullName() != null : "type without name: " + o2;
            return o1.getFullName().compareTo(o2.getFullName());
        });
        return kjts;
    }


    private ImmutableSet<PositionedString> createDLLibrarySpecsHelper(
            Collection<KeYJavaType> allKJTs,
            Path basePath) throws ProofInputException {
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        int i = 0;
        for (KeYJavaType kjt : allKJTs) {
            Type javaType = kjt.getJavaType();
            if (!(javaType instanceof TypeDeclaration)
                    || !((TypeDeclaration) javaType).isLibraryClass()) {
                continue;
            }

            final Path file = basePath.resolve(kjt.getFullName().replace(".", "/") + ".key");
            if (!Files.exists(file)) {
                continue;
            }
            RuleSource rs = RuleSourceFactory.initRuleFile(file);

            // read rule source found
            LOGGER.debug("Reading library specification file: {}", file);
            final KeYFile keyFile = new KeYFile(file.toString(), rs, null, getProfile());
            keyFile.setInitConfig(initConfig);
            warnings = warnings.union(keyFile.read());
            i += 1;
        }
        LOGGER.info("Read {} library specification files from {}", i, basePath);
        return warnings;
    }


    /**
     * For all library classes C, look for file C.key in same directory; if found, read
     * specifications from this file.
     */
    private ImmutableSet<PositionedString> createDLLibrarySpecs() throws ProofInputException {
        final Collection<KeYJavaType> allKJTs =
            initConfig.getServices().getJavaInfo().getAllKeYJavaTypes();
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        JavaService javaService = initConfig.getServices().getJavaService();
        warnings =
            warnings.union(createDLLibrarySpecsHelper(allKJTs, javaService.getBootClassPath()));

        for (Path file : javaService.getLibraryPath()) {
            warnings =
                warnings.union(createDLLibrarySpecsHelper(allKJTs, file.toAbsolutePath()));
        }
        return warnings;
    }

    private void addLoopInvariants(SpecExtractor specExtractor,
            final KeYJavaType kjt, final IProgramMethod pm)
            throws ProofInputException {
        // Loop invariants.
        final JavaASTCollector collector = new JavaASTCollector(pm.getBody(), LoopStatement.class);
        collector.start();
        for (ProgramElement loop : collector.getNodes()) {
            LoopSpecification inv = specExtractor.extractLoopInvariant(pm, (LoopStatement) loop);
            if (inv != null) {
                ((LoopStatement) loop).setLoopInvariant(inv.setTarget(kjt, pm));
            }
        }
    }

    private void addLoopContracts(SpecExtractor specExtractor,
            final ContractRegistry specRepos, final IProgramMethod pm)
            throws ProofInputException {
        // Loop contracts on loops.
        // For loop contracts on blocks, see addBlockAndLoopContracts.
        final JavaASTCollector collector = new JavaASTCollector(pm.getBody(), LoopStatement.class);
        collector.start();

        for (ProgramElement loop : collector.getNodes()) {
            final ImmutableSet<LoopContract> loopContracts =
                specExtractor.extractLoopContracts(pm, (LoopStatement) loop);

            for (LoopContract specification : loopContracts) {
                attachLoopContract(specification);
                specRepos.addFunctionalLoopContract(specification);
            }
        }
    }

    private void addBlockAndLoopContracts(SpecExtractor specExtractor,
            final ContractRegistry specRepos, final IProgramMethod pm)
            throws ProofInputException {
        // Block and loop contracts.
        final JavaASTCollector blockCollector =
            new JavaASTCollector(pm.getBody(), StatementBlock.class);
        blockCollector.start();
        for (ProgramElement block : blockCollector.getNodes()) {
            final ImmutableSet<BlockContract> blockContracts =
                specExtractor.extractBlockContracts(pm, (StatementBlock) block);

            for (BlockContract specification : blockContracts) {
                specification.getBlock().addBlockContract(specification);
                specRepos.addFunctionalBlockContract(specification);
            }

            final ImmutableSet<LoopContract> loopContracts =
                specExtractor.extractLoopContracts(pm, (StatementBlock) block);

            for (LoopContract specification : loopContracts) {
                attachLoopContract(specification);
                specRepos.addFunctionalLoopContract(specification);
            }
        }
    }

    private void addMergePointStatements(SpecExtractor specExtractor,
            final IProgramMethod pm,
            final ImmutableList<LocationVariable> methodParameters) throws ProofInputException {
        // merge point statements
        final JavaASTCollector mpsCollector =
            new JavaASTCollector(pm.getBody(), MergePointStatement.class);
        mpsCollector.start();
        for (ProgramElement mps : mpsCollector.getNodes()) {
            final ImmutableSet<MergeContract> mergeContracts = specExtractor
                    .extractMergeContracts(pm, (MergePointStatement) mps, methodParameters);
            mergeContracts.forEach(((MergePointStatement) mps)::addMergeContract);
        }
    }

    private void addLabeledBlockContracts(SpecExtractor specExtractor,
            final ContractRegistry specRepos, final IProgramMethod pm)
            throws ProofInputException {
        final JavaASTCollector labeledCollector =
            new JavaASTCollector(pm.getBody(), LabeledStatement.class);
        labeledCollector.start();
        for (ProgramElement labeled : labeledCollector.getNodes()) {
            final ImmutableSet<BlockContract> blockContracts =
                specExtractor.extractBlockContracts(pm, (LabeledStatement) labeled);
            for (BlockContract specification : blockContracts) {
                specification.getBlock().addBlockContract(specification);
                specRepos.addFunctionalBlockContract(specification);
            }
        }
    }

    private void addLabeledLoopContracts(SpecExtractor specExtractor,
            final ContractRegistry specRepos, final IProgramMethod pm)
            throws ProofInputException {
        final JavaASTCollector labeledCollector =
            new JavaASTCollector(pm.getBody(), LabeledStatement.class);
        labeledCollector.start();
        for (ProgramElement labeled : labeledCollector.getNodes()) {
            final ImmutableSet<LoopContract> loopContracts =
                specExtractor.extractLoopContracts(pm, (LabeledStatement) labeled);
            for (LoopContract specification : loopContracts) {
                attachLoopContract(specification);
                specRepos.addFunctionalLoopContract(specification);
            }
        }
    }

    /**
     * Attaches the given loop contract to its node: on-block loop contracts attach to the
     * containing {@link StatementBlock}, all others to the {@link LoopStatement} itself.
     */
    private static void attachLoopContract(final LoopContract specification) {
        if (specification.isOnBlock()) {
            specification.getBlock().addLoopContract(specification);
        } else {
            specification.getLoop().addLoopContract(specification);
        }
    }

    private void transformProgramElements(final IProgramMethod pm) throws ProofInputException {
        Services services = initConfig.getServices();
        JMLSpecFactory jsf = new JMLSpecFactory(services);
        var walker = new JavaASTWalker(pm.getBody()) {
            public ProofInputException exception = null;

            @Override
            protected void doAction(final ProgramElement node) {
                try {
                    if (node instanceof JmlAssert) {
                        jsf.translateJmlAssertCondition((JmlAssert) node, pm);
                    } else if (node instanceof SetStatement) {
                        jsf.translateSetStatement((SetStatement) node, pm);
                    }
                } catch (ProofInputException e) {
                    // Store the first exception that occurred
                    if (this.exception == null) {
                        this.exception = e;
                    }
                }
            }
        };
        walker.start();
        if (walker.exception != null) {
            throw walker.exception;
        }
    }

    private ImmutableSet<PositionedString> createSpecs(SpecExtractor specExtractor)
            throws ProofInputException {
        final JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        final SpecificationRepository specRepos =
            initConfig.getServices().getSpecificationRepository();
        final ContractRegistry contractRegistry =
            initConfig.getServices().getContractRegistry();
        final JMLSpecFactory jsf = new JMLSpecFactory(initConfig.getServices());

        // read DL library specs before any other specs
        ImmutableSet<PositionedString> warnings = createDLLibrarySpecs();

        // sort types alphabetically (necessary for deterministic names)
        final Collection<KeYJavaType> allKeYJavaTypes = javaInfo.getAllKeYJavaTypes();
        final KeYJavaType[] kjts =
            sortKJTs(allKeYJavaTypes.toArray(new KeYJavaType[0]));

        // create specifications for all types
        for (KeYJavaType kjt : kjts) {
            if (!(kjt.getJavaType() instanceof ClassDeclaration
                    || kjt.getJavaType() instanceof InterfaceDeclaration)) {
                continue;
            }

            // class invariants, represents clauses, initially clauses, ...
            final ImmutableSet<SpecificationElement> classSpecs =
                specExtractor.extractClassSpecs(kjt);
            // initially clauses are handled by the JMLSpecFactory (constructor-postcondition
            // derivation at the end of loading), everything else goes to the repo dispatcher
            ImmutableSet<SpecificationElement> toRegister = DefaultImmutableSet.nil();
            for (SpecificationElement spec : classSpecs) {
                if (spec instanceof InitiallyClause ic) {
                    jsf.addInitiallyClause(ic);
                } else {
                    toRegister = toRegister.add(spec);
                }
            }
            // Register the class-level specifications (invariants, represents clauses);
            // initially clauses were partitioned into the JMLSpecFactory above.
            registerSpecs(toRegister, initConfig.getServices());

            // Check whether a static invariant is present.
            // Later, we will only add static invariants to contracts per default if
            // there is an explicit static invariant present.
            boolean staticInvPresent = false;
            for (SpecificationElement s : classSpecs) {
                if (s instanceof ClassInvariant && ((ClassInvariant) s).isStatic()) {
                    staticInvPresent = true;
                    break;
                }
            }

            // contracts, loop invariants
            for (IProgramMethod pm : javaInfo.getAllProgramMethodsLocallyDeclared(kjt)) {
                // contracts
                final List<SpecificationElement> methodSpecs =
                    specExtractor.extractMethodSpecs(pm, staticInvPresent);
                ImmutableList<LocationVariable> params = null;
                if (!methodSpecs.isEmpty()) {
                    params = ((Contract) methodSpecs.getFirst()).getOrigVars().params;
                }
                registerSpecs(DefaultImmutableSet.fromCollection(methodSpecs),
                    initConfig.getServices());

                Type declaringType = pm.getContainerType().getJavaType();

                // Create default contracts for all methods except KeY default methods (like <init>)
                // and Object methods.
                if (methodSpecs.isEmpty()
                        && (declaringType instanceof TypeDeclaration decl && decl.isLibraryClass())
                        && !declaringType.getFullName().equals("java.lang.Object")
                        && !pm.isImplicit()) {
                    contractRegistry.addContract(specExtractor.createDefaultContract(pm,
                        initConfig.getActivatedChoices().exists(
                            choice -> choice.category().equals("soundDefaultContracts")
                                    && choice.name().toString()
                                            .equals("soundDefaultContracts:on"))));
                }

                addLoopInvariants(specExtractor, kjt, pm);
                addLoopContracts(specExtractor, contractRegistry, pm);
                addBlockAndLoopContracts(specExtractor, contractRegistry, pm);
                addMergePointStatements(specExtractor, pm, params);
                addLabeledBlockContracts(specExtractor, contractRegistry, pm);
                addLabeledLoopContracts(specExtractor, contractRegistry, pm);
                transformProgramElements(pm);
            }

            // constructor contracts
            for (IProgramMethod constructor : javaInfo.getConstructors(kjt)) {
                assert constructor.isConstructor();
                final List<SpecificationElement> constructorSpecs =
                    specExtractor.extractMethodSpecs(constructor, staticInvPresent);
                registerSpecs(DefaultImmutableSet.fromCollection(constructorSpecs),
                    initConfig.getServices());
            }
            specRepos.processJavaType(kjt);
        }

        // add initially clauses to constructor contracts
        jsf.createContractsFromInitiallyClauses();

        // update warnings to user
        final ImmutableSet<PositionedString> jmlWarnings =
            DefaultImmutableSet.fromImmutableList(specExtractor.getWarnings());
        warnings = warnings.union(jmlWarnings);
        return warnings;
    }

    /**
     * Registers the passed specification elements, dispatching each to its home: contracts to the
     * contract registry, class invariants/axioms to the class-axiom computer, loop/block/merge
     * specs to their AST nodes. Formerly {@code SpecificationRepository.addSpecs}.
     */
    private static void registerSpecs(ImmutableSet<SpecificationElement> specs,
            Services services) {
        for (SpecificationElement spec : specs) {
            if (spec instanceof Contract) {
                services.getContractRegistry().addContract((Contract) spec);
            } else if (spec instanceof ClassInvariant) {
                services.getClassAxiomComputer().addClassInvariant((ClassInvariant) spec);
            } else if (spec instanceof ClassAxiom) {
                services.getClassAxiomComputer().addClassAxiom((ClassAxiom) spec);
            } else if (spec instanceof LoopSpecification loopSpec) {
                loopSpec.getLoop().setLoopInvariant(loopSpec);
            } else if (spec instanceof BlockContract blockContract) {
                blockContract.getBlock().addBlockContract(blockContract);
            } else if (spec instanceof LoopContract loopContract) {
                if (loopContract.isOnBlock()) {
                    loopContract.getBlock().addLoopContract(loopContract);
                } else {
                    loopContract.getLoop().addLoopContract(loopContract);
                }
            } else if (spec instanceof MergeContract mergeContract) {
                mergeContract.getMergePointStatement().addMergeContract(mergeContract);
            } else {
                assert false : "unexpected spec: " + spec + "\n(" + spec.getClass() + ")";
            }
        }
    }


    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        if (initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }

        final GeneralSettings gs = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        if (gs.isUseJML()) {
            return createSpecs(new JMLSpecExtractor(initConfig));
        } else {
            return null;
        }
    }

    @Override
    public Path getInitialFile() {
        return null;
    }
}
