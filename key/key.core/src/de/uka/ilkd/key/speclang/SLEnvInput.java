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

package de.uka.ilkd.key.speclang;

import java.io.File;
import java.net.URL;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.Set;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaReduxFileCollection;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.op.IProgramMethod;
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
import de.uka.ilkd.key.util.KeYResourceManager;


/** 
 * EnvInput for standalone specification language front ends.
 */
public final class SLEnvInput extends AbstractEnvInput {
    
            
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public SLEnvInput(String javaPath,
  	      	      List<File> classPath,
  	      	      File bootClassPath,
  	      	      Profile profile,
  	      	     List<File> includes) {
	super(getLanguage() + " specifications", 
	      javaPath, 
	      classPath, 
	      bootClassPath, profile, includes);
    }
    
    
    public SLEnvInput(String javaPath,
                      Profile profile) {
	this(javaPath, null, null, profile, null);
    }    
    

    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    public static String getLanguage() {      
    	GeneralSettings gs 
        = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();
        if(gs.useJML()) {
            return "JML";
        } else {
            return "no";
        }
    }    
    
    private KeYJavaType[] sortKJTs(KeYJavaType[] kjts) {
        
        Arrays.sort(kjts, new Comparator<KeYJavaType> () {
            public int compare(KeYJavaType o1, KeYJavaType o2) {
        	assert o1.getFullName() != null : "type without name: " + o1;
        	assert o2.getFullName() != null : "type without name: " + o2;
                return o1.getFullName().compareTo(o2.getFullName());
            }
        });
        
        return kjts;
    }
    
    
    private ImmutableSet<PositionedString> createDLLibrarySpecsHelper(Set<KeYJavaType> allKJTs,
	                                    String path) 
    		throws ProofInputException {
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
        for(KeYJavaType kjt : allKJTs) {
            if(kjt.getJavaType() instanceof TypeDeclaration
               && ((TypeDeclaration)kjt.getJavaType()).isLibraryClass()) {
                final String filePath
                	= path + "/" + kjt.getFullName().replace(".", "/") 
                	       + ".key";
                RuleSource rs = null;
                
                //external or internal path?
                File file = new File(filePath);
                if(file.isFile()) {
                	rs = RuleSourceFactory.initRuleFile(file);
                } else {
                    URL url = KeYResourceManager.getManager().getResourceFile(
                				Recoder2KeY.class, 
                				filePath);
                    if(url != null) {
                	rs = RuleSourceFactory.initRuleFile(url);
                    }
                }
                
                //rule source found? -> read
                if(rs != null) {
                    final KeYFile keyFile = new KeYFile(path, rs, null, getProfile());
                    keyFile.setInitConfig(initConfig);
                    warnings = warnings.union(keyFile.read());
                }
            }
        }	
        return warnings;
    }
    
    
    /** 
     * For all library classes C, look for file C.key in same 
     * directory; if found, read specifications from this file.
     */
    private ImmutableSet<PositionedString> createDLLibrarySpecs() throws ProofInputException {
        final Set<KeYJavaType> allKJTs 
		= initConfig.getServices().getJavaInfo().getAllKeYJavaTypes();			
        ImmutableSet<PositionedString> warnings = DefaultImmutableSet.nil();
	//either boot class path or JavaRedux
	if(bootClassPath != null) {
	    warnings = warnings.union(createDLLibrarySpecsHelper(allKJTs, 
		                       bootClassPath.getAbsolutePath()));	    
	} else {
            String path = JavaReduxFileCollection.JAVA_SRC_DIR;
            if (!initConfig.getProfile().getInternalClassDirectory().isEmpty()) { 
        	path += "/" + initConfig.getProfile().getInternalClassDirectory();
            }
            warnings = warnings.union(createDLLibrarySpecsHelper(allKJTs, path));
	}
        
        //if applicable: class path
        if(classPath != null) {
            for(File file : classPath) {
               warnings = warnings.union(createDLLibrarySpecsHelper(allKJTs, file.getAbsolutePath()));
            }
        }
        return warnings;
    }
    
    
    private ImmutableSet<PositionedString> createSpecs(SpecExtractor specExtractor) 
            throws ProofInputException {
        final JavaInfo javaInfo 
            = initConfig.getServices().getJavaInfo();
        final SpecificationRepository specRepos 
            = initConfig.getServices().getSpecificationRepository();

        
        //read DL library specs before any other specs
        ImmutableSet<PositionedString> warnings = createDLLibrarySpecs();
       
        //sort types alphabetically (necessary for deterministic names)
        final Set<KeYJavaType> allKeYJavaTypes = javaInfo.getAllKeYJavaTypes();
        final KeYJavaType[] kjts = 
            sortKJTs(allKeYJavaTypes.toArray(new KeYJavaType[allKeYJavaTypes.size()]));
        
        //create specifications for all types
        for(KeYJavaType kjt : kjts) {
            if(!(kjt.getJavaType() instanceof ClassDeclaration 
        	  || kjt.getJavaType() instanceof InterfaceDeclaration)) {
        	continue;
            }

            //class invariants, represents clauses, ...
            final ImmutableSet<SpecificationElement> classSpecs 
            	= specExtractor.extractClassSpecs(kjt);
            specRepos.addSpecs(classSpecs);

            // Check whether a static invariant is present.
            // Later, we will only add static invariants to contracts per default if
            // there is an explicit static invariant present.
            boolean staticInvPresent = false;
            for (SpecificationElement s: classSpecs){
                if (s instanceof ClassInvariant && ((ClassInvariant)s).isStatic()) {
                    staticInvPresent = true;
                    break;
                }
            }

            //contracts, loop invariants
            final ImmutableList<IProgramMethod> pms 
                = javaInfo.getAllProgramMethodsLocallyDeclared(kjt);
            for(IProgramMethod pm : pms) {
                //contracts
        	final ImmutableSet<SpecificationElement> methodSpecs
        	    = specExtractor.extractMethodSpecs(pm,staticInvPresent);
        	specRepos.addSpecs(methodSpecs);

                //loop invariants
                final JavaASTCollector collector 
                    = new JavaASTCollector(pm.getBody(), LoopStatement.class);
                collector.start();
                for(ProgramElement loop : collector.getNodes()) {
                    LoopInvariant inv =
                            specExtractor.extractLoopInvariant(pm,
                        			               (LoopStatement) loop);
                    if(inv != null) {
                        specRepos.addLoopInvariant(inv.setTarget(kjt, pm));
                    }
                }

                //block contracts
                final JavaASTCollector blockCollector =
                        new JavaASTCollector(pm.getBody(), StatementBlock.class);
                blockCollector.start();
                for (ProgramElement block : blockCollector.getNodes()) {
                    final ImmutableSet<BlockContract> blockContracts =
                            specExtractor.extractBlockContracts(pm, (StatementBlock) block);
                    for (BlockContract specification : blockContracts) {
                    	specRepos.addBlockContract(specification);
                    }
                }

                final JavaASTCollector labeledCollector =
                        new JavaASTCollector(pm.getBody(), LabeledStatement.class);
                labeledCollector.start();
                for (ProgramElement labeled : labeledCollector.getNodes()) {
                    final ImmutableSet<BlockContract> blockContracts =
                            specExtractor.extractBlockContracts(pm, (LabeledStatement) labeled);
                    for (BlockContract specification : blockContracts) {
                        specRepos.addBlockContract(specification);
                    }
                }
            }

            //constructor contracts
            final ImmutableList<IProgramMethod> constructors 
            	= javaInfo.getConstructors(kjt);
            for(IProgramMethod constructor : constructors) {
        	assert constructor.isConstructor();
        	final ImmutableSet<SpecificationElement> constructorSpecs 
			= specExtractor.extractMethodSpecs(constructor, staticInvPresent);
        	specRepos.addSpecs(constructorSpecs);
            }
            specRepos.addRepresentsTermToWdChecksForModelFields(kjt);
        }

        //add initially clauses to constructor contracts
        specRepos.createContractsFromInitiallyClauses();

        //update warnings to user
        warnings = warnings.union(specExtractor.getWarnings());
        return warnings;
    }

    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------

    @Override
    public ImmutableSet<PositionedString> read() throws ProofInputException {
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
            
        final GeneralSettings gs
        = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings();

        if(gs.useJML()) {
            return createSpecs(new JMLSpecExtractor(initConfig.getServices()));
        }
        else {
           return null;
        }
    }

    @Override
    public File getInitialFile() {
       return null;
    }
}