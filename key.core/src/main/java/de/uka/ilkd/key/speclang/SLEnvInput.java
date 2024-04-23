/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.io.File;
import java.net.URL;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaReduxFileCollection;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.java.statement.SetStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.java.visitor.JavaASTWalker;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.AbstractEnvInput;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.speclang.jml.JMLSpecExtractor;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.util.KeYResourceManager;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;


/**
 * EnvInput for standalone specification language front ends.
 */
public final class SLEnvInput extends AbstractEnvInput {


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public SLEnvInput(String javaPath, List<File> classPath, File bootClassPath, Profile profile,
            List<File> includes) {
        super(getLanguage() + " specifications", javaPath, classPath, bootClassPath, profile,
            includes);
    }


    public SLEnvInput(String javaPath, Profile profile) {
        this(javaPath, null, null, profile, null);
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


    private ImmutableSet<PositionedString> createDLLibrarySpecsHelper(Set<KeYJavaType> allKJTs,
            String path) throws ProofInputException {
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        for (KeYJavaType kjt : allKJTs) {
            if (kjt.getJavaType() instanceof TypeDeclaration
                    && ((TypeDeclaration) kjt.getJavaType()).isLibraryClass()) {
                final String filePath =
                    String.format("%s/%s.key", path, kjt.getFullName().replace(".", "/"));
                RuleSource rs = null;

                // external or internal path?
                File file = new File(filePath);
                if (file.isFile()) {
                    rs = RuleSourceFactory.initRuleFile(file);
                } else {
                    URL url = KeYResourceManager.getManager().getResourceFile(Recoder2KeY.class,
                        filePath);
                    if (url != null) {
                        rs = RuleSourceFactory.initRuleFile(url);
                    }
                }

                // rule source found? -> read
                if (rs != null) {
                    final KeYFile keyFile = new KeYFile(path, rs, null, getProfile());
                    keyFile.setInitConfig(initConfig);
                    warnings = warnings.union(keyFile.read());
                }
            }
        }
        return warnings;
    }


    /**
     * For all library classes C, look for file C.key in same directory; if found, read
     * specifications from this file.
     */
    private ImmutableSet<PositionedString> createDLLibrarySpecs() throws ProofInputException {
        final Set<KeYJavaType> allKJTs =
            initConfig.getServices().getJavaInfo().getAllKeYJavaTypes();
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        // either boot class path or JavaRedux
        if (bootClassPath != null) {
            warnings = warnings
                    .union(createDLLibrarySpecsHelper(allKJTs, bootClassPath.getAbsolutePath()));
        } else {
            String path = JavaReduxFileCollection.JAVA_SRC_DIR;
            if (!initConfig.getProfile().getInternalClassDirectory().isEmpty()) {
                path += "/" + initConfig.getProfile().getInternalClassDirectory();
            }
            warnings = warnings.union(createDLLibrarySpecsHelper(allKJTs, path));
        }

        // if applicable: class path
        if (classPath != null) {
            for (File file : classPath) {
                warnings =
                    warnings.union(createDLLibrarySpecsHelper(allKJTs, file.getAbsolutePath()));
            }
        }
        return warnings;
    }

    private void addLoopInvariants(SpecExtractor specExtractor,
            final SpecificationRepository specRepos, final KeYJavaType kjt, final IProgramMethod pm)
            throws ProofInputException {
        // Loop invariants.
        final JavaASTCollector collector = new JavaASTCollector(pm.getBody(), LoopStatement.class);
        collector.start();
        for (ProgramElement loop : collector.getNodes()) {
            LoopSpecification inv = specExtractor.extractLoopInvariant(pm, (LoopStatement) loop);
            if (inv != null) {
                specRepos.addLoopInvariant(inv.setTarget(kjt, pm));
            }
        }
    }

    private void addLoopContracts(SpecExtractor specExtractor,
            final SpecificationRepository specRepos, final KeYJavaType kjt, final IProgramMethod pm)
            throws ProofInputException {
        // Loop contracts on loops.
        // For loop contracts on blocks, see addBlockAndLoopContracts.
        final JavaASTCollector collector = new JavaASTCollector(pm.getBody(), LoopStatement.class);
        collector.start();

        for (ProgramElement loop : collector.getNodes()) {
            final ImmutableSet<LoopContract> loopContracts =
                specExtractor.extractLoopContracts(pm, (LoopStatement) loop);

            for (LoopContract specification : loopContracts) {
                specRepos.addLoopContract(specification, true);
            }
        }
    }

    private void addBlockAndLoopContracts(SpecExtractor specExtractor,
            final SpecificationRepository specRepos, final IProgramMethod pm)
            throws ProofInputException {
        // Block and loop contracts.
        final JavaASTCollector blockCollector =
            new JavaASTCollector(pm.getBody(), StatementBlock.class);
        blockCollector.start();
        for (ProgramElement block : blockCollector.getNodes()) {
            final ImmutableSet<BlockContract> blockContracts =
                specExtractor.extractBlockContracts(pm, (StatementBlock) block);

            for (BlockContract specification : blockContracts) {
                specRepos.addBlockContract(specification, true);
            }

            final ImmutableSet<LoopContract> loopContracts =
                specExtractor.extractLoopContracts(pm, (StatementBlock) block);

            for (LoopContract specification : loopContracts) {
                specRepos.addLoopContract(specification, true);
            }
        }
    }

    private void addMergePointStatements(SpecExtractor specExtractor,
            final SpecificationRepository specRepos, final IProgramMethod pm,
            final ImmutableSet<SpecificationElement> methodSpecs) throws ProofInputException {
        // merge point statements
        final JavaASTCollector mpsCollector =
            new JavaASTCollector(pm.getBody(), MergePointStatement.class);
        mpsCollector.start();
        for (ProgramElement mps : mpsCollector.getNodes()) {
            final ImmutableSet<MergeContract> mergeContracts = //
                specExtractor.extractMergeContracts(pm, (MergePointStatement) mps,
                    ((Contract) methodSpecs.iterator().next()).getOrigVars().params);

            mergeContracts.forEach(specRepos::addMergeContract);
        }
    }

    private void addLabeledBlockContracts(SpecExtractor specExtractor,
            final SpecificationRepository specRepos, final IProgramMethod pm)
            throws ProofInputException {
        final JavaASTCollector labeledCollector =
            new JavaASTCollector(pm.getBody(), LabeledStatement.class);
        labeledCollector.start();
        for (ProgramElement labeled : labeledCollector.getNodes()) {
            final ImmutableSet<BlockContract> blockContracts =
                specExtractor.extractBlockContracts(pm, (LabeledStatement) labeled);
            for (BlockContract specification : blockContracts) {
                specRepos.addBlockContract(specification, true);
            }
        }
    }

    private void addLabeledLoopContracts(SpecExtractor specExtractor,
            final SpecificationRepository specRepos, final IProgramMethod pm)
            throws ProofInputException {
        final JavaASTCollector labeledCollector =
            new JavaASTCollector(pm.getBody(), LabeledStatement.class);
        labeledCollector.start();
        for (ProgramElement labeled : labeledCollector.getNodes()) {
            final ImmutableSet<LoopContract> loopContracts =
                specExtractor.extractLoopContracts(pm, (LabeledStatement) labeled);
            for (LoopContract specification : loopContracts) {
                specRepos.addLoopContract(specification, true);
            }
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

        // read DL library specs before any other specs
        ImmutableSet<PositionedString> warnings = createDLLibrarySpecs();

        // sort types alphabetically (necessary for deterministic names)
        final Set<KeYJavaType> allKeYJavaTypes = javaInfo.getAllKeYJavaTypes();
        final KeYJavaType[] kjts =
            sortKJTs(allKeYJavaTypes.toArray(new KeYJavaType[0]));

        // create specifications for all types
        for (KeYJavaType kjt : kjts) {
            if (!(kjt.getJavaType() instanceof ClassDeclaration
                    || kjt.getJavaType() instanceof InterfaceDeclaration)) {
                continue;
            }

            // class invariants, represents clauses, ...
            final ImmutableSet<SpecificationElement> classSpecs =
                specExtractor.extractClassSpecs(kjt);
            specRepos.addSpecs(classSpecs);

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
            final ImmutableList<ProgramMethod> pms =
                javaInfo.getAllProgramMethodsLocallyDeclared(kjt);
            for (IProgramMethod pm : pms) {
                // contracts
                final ImmutableSet<SpecificationElement> methodSpecs =
                    specExtractor.extractMethodSpecs(pm, staticInvPresent);
                specRepos.addSpecs(methodSpecs);

                addLoopInvariants(specExtractor, specRepos, kjt, pm);
                addLoopContracts(specExtractor, specRepos, kjt, pm);
                addBlockAndLoopContracts(specExtractor, specRepos, pm);
                addMergePointStatements(specExtractor, specRepos, pm, methodSpecs);
                addLabeledBlockContracts(specExtractor, specRepos, pm);
                addLabeledLoopContracts(specExtractor, specRepos, pm);
                transformProgramElements(pm);
            }

            // constructor contracts
            final ImmutableList<IProgramMethod> constructors = javaInfo.getConstructors(kjt);
            for (IProgramMethod constructor : constructors) {
                assert constructor.isConstructor();
                final ImmutableSet<SpecificationElement> constructorSpecs =
                    specExtractor.extractMethodSpecs(constructor, staticInvPresent);
                specRepos.addSpecs(constructorSpecs);
            }
            specRepos.addRepresentsTermToWdChecksForModelFields(kjt);
        }

        // add initially clauses to constructor contracts
        specRepos.createContractsFromInitiallyClauses();

        // update warnings to user
        final ImmutableSet<PositionedString> jmlWarnings =
            DefaultImmutableSet.fromImmutableList(specExtractor.getWarnings());
        warnings = warnings.union(jmlWarnings);
        return warnings;
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
            return createSpecs(new JMLSpecExtractor(initConfig.getServices()));
        } else {
            return null;
        }
    }

    @Override
    public File getInitialFile() {
        return null;
    }
}
